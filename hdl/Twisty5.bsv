package Twisty5;

import BRAMCore::*;
import FIFO::*;
import Vector::*;

import Common::*;

typedef 4 HartCount;
typedef Bit#(TLog#(HartCount)) HartId;

interface TwistyBus#(numeric type addr_width);
    (* always_ready *)
    method Action issue(Bit#(addr_width) address, Bool write, Word data);
    method Word response;
endinterface

interface Twisty5#(numeric type addr_width);
    (* always_ready *)
    method Bool halted;
    (* always_ready *)
    method HartId next_hart_id;
    (* always_ready *)
    method HartState next_hart_state;
endinterface

typedef enum { Left, Right } ShiftDir deriving (Bits, FShow);

typedef union tagged {
    void ResetState;
    void RunState;
    RegId LoadState;
    void HaltState;
    struct {
        RegId rd;
        UInt#(5) amt;
        bit fill;
        ShiftDir dir;
    } ShiftState;
} HartState deriving (Bits, FShow);

module mkTwisty5#(TwistyBus#(addr_width) bus) (Twisty5#(addr_width))
provisos (
    // XLEN is >= 2
    Add#(xlen_m2, 2, XLEN),
    // addr_width is <= XLEN-2
    Add#(addr_width, dropped_addr_msbs, xlen_m2)
);
    // Index of the hart that will get issued into the pipeline next.
    Reg#(HartId) next_hart <- mkReg(0);
    // Index of the hart whose bus result is expected next.
    Reg#(HartId) pending_hart <- mkReg(0);

    RegFile2H regfile <- mkRegFile2H;

    // Per-hart replicated state vectors.

    // Last word read from the bus. Valid after Reset state.
    Vector#(HartCount, Reg#(Word)) caches <- replicateM(mkReg(0));
    // Execution state.
    Vector#(HartCount, Reg#(HartState)) states <-
        replicateM(mkReg(ResetState));
    // Program counters.
    Vector#(HartCount, Reg#(Bit#(addr_width))) pcs <-
        replicateM(mkReg(0));

    // Crops a Word value for use as a smaller word address of addr_width bits.
    function Bit#(addr_width) crop_addr(Word addr);
        Bit#(xlen_m2) div4 = truncateLSB(addr);
        return truncate(div4);
    endfunction

    ///////////////////////////////////////////////////////////////////////////
    // Bus interface logic

    // Bus responses are not always_ready, largely to allow for the few cycles
    // between reset and when we start issuing actual transactions. This rule
    // notices when they become ready, copies the data into the appropriate
    // cache, and advances the pending counter.
    (* fire_when_enabled *)
    rule maintain_cache;
        let data = bus.response; // implicit condition
        for (Integer i = 0; i < valueof(HartCount); i = i + 1) begin
            if (pending_hart == fromInteger(i)) caches[i] <= data;
        end
        pending_hart <= pending_hart + 1;
    endrule

    ///////////////////////////////////////////////////////////////////////////
    // Stage 1

    // Each cycle we issue an instruction for a different hart. As there is no
    // backpressure in the pipeline, there are no conditions required for this
    // increment.
    (* fire_when_enabled, no_implicit_conditions *)
    rule advance_hart_id;
        next_hart <= next_hart + 1;
    endrule

    // FIFO connecting stage 1 to stage 2
    let stage2 <- mkLFIFO;

    // This nonsense is necessary to prevent state-observing rules in stage 1
    // from getting blocked by state-writing rules at the end of the pipeline.
    // "But a write to a register should not block a read!" you protest. Yes, I
    // know, please take it up with bsc. You'll be seeing this pattern a lot in
    // this module.
    Wire#(HartState) cur_state <- mkBypassWire;
    (* fire_when_enabled, no_implicit_conditions *)
    rule read_state_mux;
        for (Integer i = 0; i < valueof(HartCount); i = i + 1) begin
            if (next_hart == fromInteger(i)) cur_state <= states[i];
        end
    endrule

    // TODO I would very much like to no_implicit_conditions this, but the FIFO
    // enq looks like it can block. It can't, in our usage, but the FIFO type
    // does not express this.
    (* fire_when_enabled *)
    rule do_stage_1;
        InstFields fields = unpack(caches[next_hart]);
        regfile.read(next_hart, fields.rs1, fields.rs2);
        stage2.enq(next_hart);
    endrule

    ///////////////////////////////////////////////////////////////////////////
    // Stage 2

    // Extract register values for stage2 to avoid rule-blocking
    let stage2_state <- mkWire;
    let stage2_pc <- mkWire;
    rule extract_stage2_state;
        for (Integer i = 0; i < valueOf(HartCount); i = i + 1) begin
            if (stage2.first == fromInteger(i)) begin
                stage2_state <= states[i];
                stage2_pc <= pcs[i];
            end
        end
    endrule

    // The main execution path, factored out of the rule below to decrease
    // indentation creep.
    function run_body(hart);
        actionvalue
            let inst = caches[hart];

            InstFields fields = unpack(inst);
            Word imm_i = signExtend(inst[31:20]);
            Word imm_u = {inst[31:12], 0};
            Word imm_j = {
                signExtend(inst[31]), inst[19:12], inst[20], inst[30:21], 1'b0};
            Word imm_b = {
                signExtend(inst[31]), inst[7], inst[30:25], inst[11:8], 1'b0};

            let next_pc = stage2_pc + 1; // we will MUTATE this for jumps!

            let {x1, x2} = regfile.read_result;
            let pc00 = {stage2_pc, 2'b00};

            let comp_rhs = case (fields.opcode) matches
                'b1100011: return x2; // Bxx
                'b0110011: return x2; // ALU reg
                'b0010011: return imm_i; // ALU imm
                default: return ?;
            endcase;

            // Force structural sharing between the subtraction circuit and the
            // comparators.
            let difference = zeroExtend(x1) + {1'b1, ~comp_rhs} + 1;
            let signed_less_than = unpack(
                (x1[31] ^ comp_rhs[31]) != 0 ? x1[31] : difference[32]);
            let unsigned_less_than = unpack(difference[32]);

            // Behold, the Big Fricking RV32I Case Discriminator!
            let next_state = tagged RunState;
            let mem_write = False;
            let mem_data = ?;
            let other_addr = tagged Invalid;
            case (fields.opcode) matches
                // LUI
                'b0110111: regfile.write(hart, fields.rd, imm_u);
                // AUIPC
                'b0010111: regfile.write(hart, fields.rd, extend(pc00 + truncate(imm_u)));
                // JAL
                'b1101111: begin
                    regfile.write(hart, fields.rd, extend({stage2_pc + 1, 2'b00}));
                    next_pc = truncateLSB(pc00 + truncate(imm_j));
                end
                // JALR
                'b1100111: begin
                    regfile.write(hart, fields.rd, extend({stage2_pc + 1, 2'b00}));
                    next_pc = crop_addr(x1 + imm_i);
                end
                // Bxx
                'b1100011: begin
                    let condition = case (fields.funct3) matches
                        'b000: return x1 == x2;
                        'b001: return x1 != x2;
                        'b100: return signed_less_than;
                        'b101: return !signed_less_than;
                        'b110: return unsigned_less_than;
                        'b111: return !unsigned_less_than;
                        default: return ?;
                    endcase;
                    if (condition) next_pc = crop_addr(extend(pc00) + imm_b);
                end
                // Lx
                'b0000011: begin
                    case (fields.funct3) matches
                        'b010: begin // LW
                            next_state = tagged LoadState fields.rd;
                            other_addr = tagged Valid crop_addr(x1 + imm_i);
                        end
                        default: next_state = tagged HaltState;
                    endcase
                end
                // Sx
                'b0100011: begin
                    case (fields.funct3) matches
                        'b010: begin // SW
                            next_state = tagged ResetState;
                            other_addr = tagged Valid crop_addr(x1 + imm_i);
                            mem_write = True;
                            mem_data = x2;
                        end
                        default: next_state = tagged HaltState;
                    endcase
                end
                // ALU reg/immediate
                'b0?10011: begin
                    let is_reg = fields.opcode[5];
                    let rhs = is_reg == 1 ? x2 : imm_i;

                    let alu_result = ?;
                    case (fields.funct3) matches
                        'b000: begin // ADDI / ADD / SUB
                            let sub = is_reg & fields.funct7[5];
                            alu_result = sub != 0 ? truncate(difference) : x1 + rhs;
                        end
                        'b001: begin
                            let shift_dist = rhs[4:0];
                            next_state = tagged ShiftState {
                                amt: unpack(shift_dist),
                                rd: fields.rd,
                                fill: 0,
                                dir: Left
                            };
                            alu_result = x1;
                        end
                        // SLTI / SLT
                        'b010: alu_result = signed_less_than ? 1 : 0;
                        // SLTIU / SLTU
                        'b011: alu_result = unsigned_less_than ? 1 : 0;
                        'b100: alu_result = x1 ^ rhs; // XORI / XOR
                        'b101: begin
                            let shift_dist = rhs[4:0];
                            let fill = fields.funct7[5] & x1[31];
                            next_state = tagged ShiftState {
                                amt: unpack(shift_dist),
                                rd: fields.rd,
                                fill: fill,
                                dir: Right
                            };
                            alu_result = x1;
                        end
                        'b110: alu_result = x1 | rhs; // ORI / OR
                        'b111: alu_result = x1 & rhs; // ANDI / AND
                    endcase
                    regfile.write(hart, fields.rd, alu_result);
                end
                default: next_state = tagged HaltState;
            endcase

            let a = fromMaybe(next_pc, other_addr);
            return tuple6(hart, a, mem_write, mem_data, next_pc, next_state);
        endactionvalue
    endfunction

    (* fire_when_enabled *)
    rule do_stage_2;
        let hart = stage2.first;
        stage2.deq;

        let t <- case (stage2_state) matches
            tagged ResetState: return (actionvalue
                return tuple6(hart, stage2_pc, False, ?, stage2_pc,
                    tagged RunState);
            endactionvalue);
            tagged LoadState .rd: return (actionvalue
                regfile.write(hart, rd, caches[hart]);
                return tuple6(hart, stage2_pc, False, ?, stage2_pc,
                    tagged RunState);
            endactionvalue);
            tagged ShiftState .flds: return (actionvalue
                let {x1, x2} = regfile.read_result;
                let r = case (flds.dir) matches
                    Left: {truncate(x1), 1'b0};
                    Right: {flds.fill, truncateLSB(x1)};
                endcase;
                if (flds.amt != 0) regfile.write(hart, flds.rd, r);

                let next = (flds.amt == 0) ? tagged RunState
                    : tagged ShiftState {
                        amt: flds.amt - 1,
                        rd: flds.rd,
                        dir: flds.dir,
                        fill: flds.fill
                    };
                
                // We'll issue a dummy fetch for the next instruction during
                // every cycle of the shift, to maintain transaction ordering.
                return tuple6(hart, stage2_pc, False, ?, stage2_pc, next);
            endactionvalue);
            tagged RunState: return run_body(hart);
        endcase;

        // This seam is where you could split off a third stage by inserting a
        // FIFO.

        let {_hart, addr, write, data, next_pc, next_state} = t;
        pcs[hart] <= next_pc;
        states[hart] <= next_state;
        bus.issue(addr, write, data);
    endrule

    method HartId next_hart_id = next_hart;
    method HartState next_hart_state = states[next_hart];
    method Bool halted = states[next_hart] matches HaltState ? True : False;
endmodule

///////////////////////////////////////////////////////////////////////////////
// 2R1W register file designed around iCE40 pseudo-dual-port block RAM.

interface RegFile2H;
    // Starts a read of GPRs 'rs1' and 'rs2' for 'hart'. The contents will be
    // available after the next clock edge on 'read_result'.
    (* always_ready *)
    method Action read(HartId hart, RegId rs1, RegId rs2);

    // Last values read from GPRs.
    (* always_ready *)
    method Tuple2#(Word, Word) read_result;

    // Sets register 'index' to 'value'.
    (* always_ready *)
    method Action write(HartId hart, RegId index, Word value);
endinterface

// BRAM-based register file implementation.
(* synthesize *)
module mkRegFile2H (RegFile2H);
    BRAM_DUAL_PORT#(Tuple2#(HartId, RegId), Word) rf0 <-
        mkBRAMCore2Load(valueof(RegCount) * valueof(HartCount), False,
            "../hdl/zero-register-set.readmemb", True);
    BRAM_DUAL_PORT#(Tuple2#(HartId, RegId), Word) rf1 <-
        mkBRAMCore2Load(valueof(RegCount) * valueof(HartCount), False,
            "../hdl/zero-register-set.readmemb", True);

    method Action read(HartId hart, RegId rs1, RegId rs2);
        rf0.a.put(False, tuple2(hart, rs1), ?);
        rf1.a.put(False, tuple2(hart, rs2), ?);
    endmethod

    method Action write(HartId hart, RegId index, Word value);
        if (index != 0) begin
            rf0.b.put(True, tuple2(hart, index), value);
            rf1.b.put(True, tuple2(hart, index), value);
        end
    endmethod

    method Tuple2#(Word, Word) read_result = tuple2(rf0.a.read, rf1.a.read);
endmodule

endpackage

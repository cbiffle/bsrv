package Twisty5;

import BRAMCore::*;
import FIFO::*;
import Vector::*;

import Common::*;

typedef 4 HartCount;
typedef Bit#(TLog#(HartCount)) HartId;

interface TwistyBus#(numeric type addr_width);
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

typedef union tagged {
    void ResetState;
    void RunState;
    RegId LoadState;
    void HaltState;
} HartState deriving (Bits, FShow);

typedef enum {
    WriteAluResult,
    WriteCacheContents
} WriteOverride deriving (Bits, FShow);

module mkTwisty5#(TwistyBus#(addr_width) bus) (Twisty5#(addr_width))
provisos (
    // XLEN is >= 2
    Add#(xlen_m2, 2, XLEN),
    // addr_width is <= XLEN-2
    Add#(addr_width, dropped_addr_msbs, xlen_m2)
);
    Reg#(HartId) next_hart <- mkReg(0);
    Reg#(HartId) pending_hart <- mkReg(0);

    Vector#(HartCount, Reg#(Maybe#(Word))) caches <-
        replicateM(mkReg(tagged Invalid));
    Vector#(HartCount, Reg#(HartState)) states <-
        replicateM(mkReg(ResetState));
    Vector#(HartCount, Reg#(Bit#(addr_width))) pcs <-
        replicateM(mkReg(0));

    RegFile2H regfile <- mkRegFile2H;

    Vector#(HartCount, PulseWire) cache_clear <- replicateM(mkPulseWire);
    RWire#(Word) bus_response <- mkRWire;
    PulseWire response_ack <- mkPulseWire;

    rule copy_bus_response;
        bus_response.wset(bus.response);
    endrule

    let stage2 <- mkLFIFO;

    // Crops a Word value for use as a smaller word address of addr_width bits.
    function Bit#(addr_width) crop_addr(Word addr);
        Bit#(xlen_m2) div4 = truncateLSB(addr);
        return truncate(div4);
    endfunction

    Wire#(HartState) cur_state <- mkWire;
    for (Integer i = 0; i < valueof(HartCount); i = i + 1) begin
        (* fire_when_enabled, no_implicit_conditions *)
        rule read_state (next_hart == fromInteger(i));
            cur_state <= states[i];
        endrule
    end

    (* fire_when_enabled, no_implicit_conditions *)
    rule advance_hart_id;
        next_hart <= next_hart + 1;
    endrule

    for (Integer i = 0; i < valueof(HartCount); i = i + 1) begin
        (* fire_when_enabled *)
        rule maintain_cache;
            if (pending_hart == fromInteger(i) &&& bus_response.wget matches
                tagged Valid .data) begin
                caches[i] <= tagged Valid data;
            end else if (cache_clear[i]) caches[i] <= tagged Invalid;
        endrule

        (* fire_when_enabled *)
        rule maintain_cache_a (pending_hart == fromInteger(i) &&&
            bus_response.wget matches tagged Valid .*);
            response_ack.send;
        endrule
    end

    (* fire_when_enabled *)
    rule ack (response_ack);
        pending_hart <= pending_hart + 1;
    endrule

    (* fire_when_enabled *)
    rule boot (
        cur_state matches tagged ResetState
    );
        stage2.enq(next_hart);
    endrule

    (* fire_when_enabled *)
    rule run (
        cur_state matches tagged RunState
        &&& caches[next_hart] matches tagged Valid .inst
    );
        InstFields fields = unpack(inst);
        regfile.read(next_hart, fields.rs1, fields.rs2);
        stage2.enq(next_hart);
    endrule

    (* fire_when_enabled *)
    rule finish_load (
        cur_state matches tagged LoadState .rd
        &&& caches[next_hart] matches tagged Valid .*
    );
        stage2.enq(next_hart);
    endrule

    let stage2_state <- mkWire;
    let stage2_pc <- mkWire;

    for (Integer i = 0; i < valueOf(HartCount); i = i + 1) begin
        rule extract_stage2_state (stage2.first == fromInteger(i));
            stage2_state <= states[i];
            stage2_pc <= pcs[i];
        endrule
    end

    let stage3 <- mkLFIFO;

    (* fire_when_enabled *)
    rule boot_stage2 (
        stage2.first matches .hart
        &&& stage2_state matches tagged ResetState
    );
        stage2.deq;
        stage3.enq(tuple6(hart, stage2_pc, False, ?, stage2_pc, tagged RunState));
        cache_clear[hart].send;
    endrule

    (* fire_when_enabled *)
    rule run_stage2 (
        stage2.first matches .hart
        &&& stage2_state matches tagged RunState
    );
        stage2.deq;

        let inst = fromMaybe(?, caches[hart]);

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

        // Force structural sharing for the shifters. Shifters are expensive,
        // we only want one generated.
        let shifter_lhs = case (fields.funct3) matches
            'b001: return reverseBits(x1);
            'b100: return x1;
            default: return ?;
        endcase;
        bit shift_fill = msb(shifter_lhs) & fields.funct7[5];
        Int#(33) shift_ext = unpack({shift_fill, shifter_lhs});
        let shifter_out = truncate(pack(shift_ext >> comp_rhs[4:0]));

        // Behold, the Big Fricking RV32I Case Discriminator!
        let next_state = tagged RunState;
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
                        stage3.enq(tuple6(hart, crop_addr(x1 + imm_i), False, ?,
                            next_pc, next_state));
                    end
                    default: next_state = tagged HaltState;
                endcase
            end
            // Sx
            'b0100011: begin
                case (fields.funct3) matches
                    'b010: begin // SW
                        next_state = tagged ResetState;
                        stage3.enq(tuple6(hart, crop_addr(x1 + imm_i), True, x2,
                            next_pc, next_state));
                    end
                    default: next_state = tagged HaltState;
                endcase
            end
            // ALU reg/immediate
            'b0?10011: begin
                let is_reg = fields.opcode[5];
                let rhs = is_reg == 1 ? x2 : imm_i;

                let alu_result = case (fields.funct3) matches
                    'b000: begin // ADDI / ADD / SUB
                        let sub = is_reg & fields.funct7[5];
                        return sub != 0 ? truncate(difference) : x1 + rhs;
                    end
                    'b001: return reverseBits(shifter_out); // SLLI / SLL
                    // SLTI / SLT
                    'b010: return signed_less_than ? 1 : 0;
                    // SLTIU / SLTU
                    'b011: return unsigned_less_than ? 1 : 0;
                    'b100: return x1 ^ rhs; // XORI / XOR
                    'b101: return shifter_out;
                    'b110: return x1 | rhs; // ORI / OR
                    'b111: return x1 & rhs; // ANDI / AND
                endcase;
                regfile.write(hart, fields.rd, alu_result);
            end
            default: next_state = tagged HaltState;
        endcase

        // Issue a fetch if we're continuing on. Load/store will have issued
        // their own.
        if (next_state matches tagged RunState) begin
            stage3.enq(tuple6(hart, next_pc, False, ?, next_pc, next_state));
        end

        cache_clear[hart].send;
    endrule

    (* fire_when_enabled *)
    rule run_stage2_ld (
        stage2.first matches .hart
        &&& stage2_state matches tagged LoadState .rd
    );
        stage2.deq;
        stage3.enq(tuple6(hart, stage2_pc, False, ?, stage2_pc, tagged RunState));

        let loaded_data = fromMaybe(?, caches[hart]);
        regfile.write(hart, rd, loaded_data);
        cache_clear[hart].send;
    endrule

    (* fire_when_enabled *)
    rule writeback;
        let {hart, addr, write, data, next_pc, next_state} = stage3.first;
        stage3.deq;
        pcs[hart] <= next_pc;
        states[hart] <= next_state;
        bus.issue(addr, write, data);
    endrule

    method HartId next_hart_id = next_hart;
    method HartState next_hart_state = states[next_hart];
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

// Corny5 is a very simple RISC-V RV32I implementation in Bluespec, designed
// for synthesis on the iCE40 FPGA family.
//
// Corny5 is intended to be a straight naive implementation of the RV32I spec
// without a lot of elaboration and optimization. The main "clever" thing
// happening here is overlapped fetch and execute, saving one clock per cycle
// on everything but loads and stores. (Most instructions take 2 cycles; loads
// and stores take 3.) Otherwise, it's intended to be readable next to the
// RV32I spec.

package Corny5;

import Common::*;
import Rvfi::*;

///////////////////////////////////////////////////////////////////////////////
// The Corny5 CPU Core.

// Core debug outputs.
interface Corny5#(numeric type addr_width);
    // Internal state of core, for debugging.
    (* always_ready *)
    method State core_state;

    // Currently latched instruction, for debugging.
    (* always_ready *)
    method Word core_inst;
endinterface

// Execution states of the CPU.
typedef union tagged {
    void JustFetchState; // Reset, or second cycle of store.
    void RegState;       // Reading instruction, selecting registers.
    void ExecuteState;   // Executing first instruction cycle.
    struct {
        Bit#(2) addr_lsbs;
    } LoadState;         // Second cycle for loads.
    void HaltState;      // Something has gone wrong.
} State deriving (Bits, FShow, Eq);

module mkCorny5#(
    DinkyBus#(addr_width) bus,
    RvfiEmit#(32, 32) rvfi
) (Corny5#(addr_width))
provisos (
    // XLEN is >= 2
    Add#(xlen_m2, 2, XLEN),
    // addr_width is <= XLEN-2
    Add#(addr_width, dropped_addr_msbs, xlen_m2)
);
    ///////////////////////////////////////////////////////////////////////////
    // State elements.

    // State of execution state machine.
    Reg#(State) state <- mkReg(JustFetchState);
    // Address of current instruction. Note that this is a word address, not a
    // byte address, so it is missing its two LSBs.
    Reg#(Bit#(addr_width)) pc <- mkReg(0);
    // Copy of PC for test, should be optimized out in synth
    Reg#(Bit#(addr_width)) last_pc <- mkRegU;
    // Latched instruction being executed -- only valid in states past
    // RegState!
    Reg#(Word) inst <- mkRegU;
    // General purpose registers (two-read one-write file).
    RegFile2 regfile <- mkRegFile2;

    ///////////////////////////////////////////////////////////////////////////
    // Internal buses and combinational circuits.

    // PC extended as a byte address, which is the version RISC-V instructions
    // want to use for arithmetic.
    let pc00 = {pc, 2'b00};

    // Instruction fields.
    InstFields fields = unpack(inst);

    // Various immediate decodes
    Word imm_i = signExtend(inst[31:20]);
    Word imm_s = signExtend({inst[31:25], inst[11:7]});
    Word imm_u = {inst[31:12], 0};
    Word imm_j = {
        signExtend(inst[31]), inst[19:12], inst[20], inst[30:21], 1'b0};
    Word imm_b = {
        signExtend(inst[31]), inst[7], inst[30:25], inst[11:8], 1'b0};

    // Crops a Word value for use as a smaller word address of addr_width bits.
    function Bit#(addr_width) crop_addr(Word addr);
        Bit#(xlen_m2) div4 = truncateLSB(addr);
        return truncate(div4);
    endfunction

    ///////////////////////////////////////////////////////////////////////////
    // Core execution rules.

    // Reusable snippet for any state that wants to start an overlapping
    // instruction fetch (which is most of them).
    function Action fetch_next_instruction(Bit#(addr_width) next_pc);
        return action
            bus.issue(next_pc, 4'b0000, ?);
            pc <= next_pc;
            state <= RegState;
        endaction;
    endfunction

    (* fire_when_enabled, no_implicit_conditions *)
    rule just_fetch (state matches JustFetchState);
        fetch_next_instruction(pc);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule read_reg (state matches RegState);
        // Latch the instruction we've fetched from memory.
        inst <= bus.response;
        // Note that in this state, we address the register file directly from
        // the data bus return path -- because we don't have the instruction
        // latched yet!
        regfile.read(bus.response[19:15], bus.response[24:20]);
        state <= ExecuteState;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule execute (state matches ExecuteState);
        last_pc <= pc;
        Bit#(addr_width) next_pc = pc + 1; // we will MUTATE this for jumps!

        let {x1, x2} = regfile.read_result;

        // Behold, the Big Fricking RV32I Case Discriminator!
        let halting = False;
        let loading = False;
        let storing = False;
        let load_lsbs = 0;
        Maybe#(Tuple2#(RegId, Word)) regwrite = tagged Invalid;
        case (fields.opcode) matches
            // LUI
            'b0110111: regwrite = tagged Valid tuple2(fields.rd, imm_u);
            // AUIPC
            'b0010111: regwrite = tagged Valid tuple2(fields.rd, extend(pc00) + imm_u);
            // JAL
            'b1101111: begin
                regwrite = tagged Valid tuple2(fields.rd, extend({pc + 1, 2'b00}));
                next_pc = truncateLSB(pc00 + truncate(imm_j));
            end
            // JALR
            'b1100111: begin
                regwrite = tagged Valid tuple2(fields.rd, extend({pc + 1, 2'b00}));
                next_pc = crop_addr(x1 + imm_i);
            end
            // Bxx
            'b1100011: begin
                let condition = case (fields.funct3) matches
                    'b000: return x1 == x2;
                    'b001: return x1 != x2;
                    'b100: return toSigned(x1) < toSigned(x2);
                    'b101: return !(toSigned(x1) < toSigned(x2));
                    'b110: return x1 < x2;
                    'b111: return !(x1 < x2);
                    // There are two condition codes for branches that are
                    // undefined in RV32I. Let's treat them as not-taken.
                    // (Making an explicit decision here simplifies the
                    // output.)
                    default: return False;
                endcase;
                if (condition) next_pc = crop_addr(extend(pc00) + imm_b);
            end
            // Lx
            'b0000011: begin
                case (fields.funct3) matches
                    'b?00: begin // LB / LBU
                        Word ea = x1 + imm_i;
                        bus.issue(crop_addr(ea), 4'b0000, ?);
                        load_lsbs = ea[1:0];
                        loading = True;
                    end
                    'b?01: begin // LH / LHU
                        Word ea = x1 + imm_i;
                        if (is_aligned(ea, 1)) begin
                            bus.issue(crop_addr(ea), 4'b0000, ?);
                            load_lsbs = ea[1:0];
                            loading = True;
                        end else halting = True;
                    end
                    'b010: begin // LW
                        Word ea = x1 + imm_i;
                        if (is_aligned(ea, 2)) begin
                            bus.issue(crop_addr(ea), 4'b0000, ?);
                            loading = True;
                        end else halting = True;
                    end
                    default: halting = True;
                endcase
            end
            // Sx
            'b0100011: begin
                case (fields.funct3) matches
                    'b010: begin // SW
                        bus.issue(crop_addr(x1 + imm_s), 4'b1111, x2);
                        storing = True;
                    end
                    default: halting = True;
                endcase
            end
            // ALU reg/immediate
            'b0?10011: begin
                let is_reg = fields.opcode[5];
                let rhs = is_reg == 1 ? x2 : imm_i;

                let alu_result = case (fields.funct3) matches
                    'b000: begin // ADDI / ADD / SUB
                        let sub = is_reg & fields.funct7[5];
                        return sub != 0 ? x1 - rhs : x1 + rhs;
                    end
                    'b001: return x1 << rhs[4:0]; // SLLI / SLL
                    // SLTI / SLT
                    'b010: return toSigned(x1) < toSigned(rhs) ? 1 : 0;
                    // SLTIU / SLTU
                    'b011: return x1 < rhs ? 1 : 0;
                    'b100: return x1 ^ rhs; // XORI / XOR
                    'b101: if (fields.funct7[5] != 0) begin // SRAI / SRA
                        return pack(toSigned(x1) >> rhs[4:0]);
                    end else begin // SRLI / SRL
                        return x1 >> rhs[4:0];
                    end
                    'b110: return x1 | rhs; // ORI / OR
                    'b111: return x1 & rhs; // ANDI / AND
                endcase;
                regwrite = tagged Valid tuple2(fields.rd, alu_result);
            end
            default: halting = True;
        endcase

        if (regwrite matches tagged Valid {.rd, .x})
            regfile.write(rd, x);

        if (!loading) rvfi.retire(RvfiRetire
            { insn: inst
            , trap: False
            , halt: halting
            , intr: False
            , mode: MMode
            , ixl: 0
            , rs1: tuple2(fields.rs1, x1)
            , rs2: tuple2(fields.rs2, x2)
            , rd: fromMaybe(tuple2(0, ?), regwrite)
            , pc_before: extend(pc00)
            , pc_after: extend({next_pc, 2'b00})
            , mem_addr: x1 + imm_s
            , mem_wmask: storing ? -1 : 0
            , mem_wdata: x2
            , mem_rmask: 0
            , mem_rdata: ?
            });

        if (halting) state <= HaltState;
        else if (loading) begin
            pc <= next_pc;
            state <= tagged LoadState { addr_lsbs: load_lsbs };
        end else if (storing) begin
            pc <= next_pc;
            state <= JustFetchState;
        end else begin
            fetch_next_instruction(next_pc);
        end
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule finish_load (state matches tagged LoadState { addr_lsbs: .lsbs });
        let size = fields.funct3;
        let rmask = case (size) matches
            'b?00: 1 << lsbs;
            'b?01: 'b11 << lsbs;
            'b010: 'b1111;
        endcase;

        let loaded_value = case (size) matches
            'b?00: begin
                let uns = size[2] != 0;
                let byteval = case (lsbs) matches
                    'b00: bus.response[7:0];
                    'b01: bus.response[15:8];
                    'b10: bus.response[23:16];
                    'b11: bus.response[31:24];
                endcase;
                return uns ? extend(byteval) : signExtend(byteval);
            end
            'b?01: begin
                let uns = size[2] != 0;
                let halfval = case (lsbs) matches
                    'b00: bus.response[15:0];
                    'b10: bus.response[31:16];
                endcase;
                return uns ? extend(halfval) : signExtend(halfval);
            end
            'b010: bus.response;
        endcase;

        regfile.write(fields.rd, loaded_value);
        fetch_next_instruction(pc);

        let {x1, x2} = regfile.read_result;
        rvfi.retire(RvfiRetire
            { insn: inst
            , trap: False
            , halt: False
            , intr: False
            , mode: MMode
            , ixl: 0
            , rs1: tuple2(fields.rs1, x1)
            , rs2: tuple2(fields.rs2, x2)
            , rd: tuple2(fields.rd, loaded_value)
            , pc_before: extend({last_pc, 2'b00})
            , pc_after: extend({pc, 2'b00})
            , mem_addr: (x1 + imm_i) & ~'b11
            , mem_wmask: 0
            , mem_wdata: x2 // whatevs
            , mem_rmask: rmask
            , mem_rdata: bus.response
            });

    endrule

    ///////////////////////////////////////////////////////////////////////////
    // External port connections.

    method State core_state = state;

    method Word core_inst = inst;
endmodule

endpackage

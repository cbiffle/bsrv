// Tangy5 is a very simple RISC-V RV32I implementation in Bluespec, designed
// for synthesis on the iCE40 FPGA family.
//
// This is derived from the Dinky5 core, but aims at producing a faster core
// that still fits within an hx1k. Compared to Dinky5...
//
// - Uses 2 additional BRAM tiles to make a 3-port register file.
// - Instructions take one fewer cycle for 33% more MIPS at same frequency.
// - Identical bus interface so the two cores are interchangeable.

package Tangy5;

import BRAMCore::*;
import FShow::*;
import Vector::*;

import Common::*;

///////////////////////////////////////////////////////////////////////////////
// The Tangy5 CPU Core.

// Tangy5 can be customized in terms of its implemented address bus width. The
// address bus is in terms of _words,_ i.e. the maximum width for XLEN of 32 is
// 30.
interface Tangy5#(numeric type addr_width);
    // Internal state of core, for debugging.
    (* always_ready *)
    method OneHotState core_state;

    // Currently latched instruction, for debugging.
    (* always_ready *)
    method Word core_inst;
endinterface

// Execution states of the CPU. These enumerate bit positions in the actual
// one-hot state used by the circuit.
typedef enum {
    JustFetchState, // Reset, or second cycle of store.
    RegState,       // Reading instruction, selecting registers.
    ExecuteState,   // Executing first instruction cycle.
    LoadState,      // Second cycle for loads.
    HaltState       // Something has gone wrong.
} State deriving (Bounded, Bits, FShow, Eq);

instance OneHotIndex#(State, 5);
endinstance
typedef Bit#(5) OneHotState;

module mkTangy5#(DinkyBus#(addr_width) bus) (Tangy5#(addr_width))
provisos (
    // XLEN is >= 2
    Add#(xlen_m2, 2, XLEN),
    // addr_width is <= XLEN-2
    Add#(addr_width, dropped_addr_msbs, xlen_m2)
);
    ///////////////////////////////////////////////////////////////////////////
    // State elements.

    // State of execution state machine.
    Reg#(OneHotState) state <- mkReg(onehot_state(JustFetchState));
    // Address of current instruction. Note that this is a word address, not a
    // byte address, so it is missing its two LSBs.
    Reg#(Bit#(addr_width)) pc <- mkReg(0);
    // Latched instruction being executed -- only valid in states past
    // RegState!
    Reg#(Word) inst <- mkRegU;
    // Our early guess at the next PC value.
    Reg#(Bit#(addr_width)) pc_1 <- mkRegU;

    // General purpose registers.
    RegFile2 regfile <- mkRegFile2;

    ///////////////////////////////////////////////////////////////////////////
    // Internal buses and combinational circuits.

    // PC extended as a byte address, which is the version RISC-V instructions
    // want to use for arithmetic.
    let pc00 = {pc, 2'b00};

    // Instruction fields.
    let inst_opcode = inst[6:0];
    let inst_rd = inst[11:7];
    let inst_funct3 = inst[14:12];
    let inst_rs1 = inst[19:15];
    let inst_funct7 = inst[31:25];

    // Various immediate decodes
    Word imm_i = signExtend(inst[31:20]);
    Word imm_s = signExtend({inst[31:25], inst[11:7]});
    Word imm_u = {inst[31:12], 0};
    Word imm_j = {
        signExtend(inst[31]), inst[19:12], inst[20], inst[30:21], 1'b0};
    Word imm_b = {
        signExtend(inst[31]), inst[7], inst[30:25], inst[11:8], 1'b0};

    ///////////////////////////////////////////////////////////////////////////
    // Core execution rules.

    // Reusable snippet for any state that wants to start an overlapping
    // instruction fetch (which is most of them).
    function Action fetch_next_instruction(Bit#(addr_width) next_pc);
        return action
            bus.issue(next_pc, 4'b0000, ?);
            pc <= next_pc;
            state <= onehot_state(RegState);
        endaction;
    endfunction


    // Explain our use of one-hot state encoding to the compiler.
    (* mutually_exclusive = "just_fetch, read_reg, execute, finish_load" *)

    (* fire_when_enabled, no_implicit_conditions *)
    rule just_fetch (is_onehot_state(state, JustFetchState));
        fetch_next_instruction(pc);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule read_reg (is_onehot_state(state, RegState));
        inst <= bus.response;
        // Note that in this state, we address the register file directly from
        // the data bus return path -- because we don't have the instruction
        // latched yet!
        regfile.read(bus.response[19:15], bus.response[24:20]);
        state <= onehot_state(ExecuteState);
        pc_1 <= pc + 1;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule execute (is_onehot_state(state, ExecuteState));
        let next_pc = pc_1; // we will MUTATE this for jumps!

        let {x1, x2} = regfile.read_result;

        let comp_rhs = case (inst_opcode) matches
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
        let shifter_lhs = case (inst_funct3) matches
            'b001: return reverseBits(x1);
            'b100: return x1;
            default: return ?;
        endcase;
        bit shift_fill = msb(shifter_lhs) & inst_funct7[5];
        Int#(33) shift_ext = unpack({shift_fill, shifter_lhs});
        let shifter_out = truncate(pack(shift_ext >> comp_rhs[4:0]));

        // Behold, the Big Fricking RV32I Case Discriminator!
        let halting = False;
        let loading = False;
        let storing = False;
        case (inst_opcode) matches
            // LUI
            'b0110111: begin
                regfile.write(inst_rd, imm_u);
            end
            // AUIPC
            'b0010111: begin
                regfile.write(inst_rd, extend(pc00) + imm_u);
            end
            // JAL
            'b1101111: begin
                regfile.write(inst_rd, extend({pc_1, 2'b00}));
                next_pc = truncateLSB(pc00 + truncate(imm_j));
            end
            // JALR
            'b1100111: begin
                regfile.write(inst_rd, extend({pc_1, 2'b00}));
                Word full_ea = x1 + imm_i;
                Bit#(xlen_m2) word_ea = truncateLSB(full_ea);
                next_pc = truncate(word_ea);
            end
            // Bxx
            'b1100011: begin
                let condition = case (inst_funct3) matches
                    'b000: return x1 == comp_rhs;
                    'b001: return x1 != comp_rhs;
                    'b100: return signed_less_than;
                    'b101: return !signed_less_than;
                    'b110: return unsigned_less_than;
                    'b111: return !unsigned_less_than;
                    default: return ?;
                endcase;
                if (condition) next_pc = truncateLSB(pc00 + truncate(imm_b));
            end
            // Lx
            'b0000011: begin
                case (inst_funct3) matches
                    'b010: begin // LW
                        let byte_ea = x1 + imm_i;
                        Bit#(xlen_m2) word_ea = truncateLSB(byte_ea);
                        bus.issue(truncate(word_ea), 4'b0000, ?);
                        loading = True;
                    end
                    default: halting = True;
                endcase
            end
            // Sx
            'b0100011: begin
                case (inst_funct3) matches
                    'b010: begin // SW
                        let byte_ea = x1 + imm_s;
                        Bit#(xlen_m2) word_ea = truncateLSB(byte_ea);
                        bus.issue(truncate(word_ea), 4'b1111, x2);
                        storing = True;
                    end
                    default: halting = True;
                endcase
            end
            // ALU reg/immediate
            'b0?10011: begin
                let is_reg = inst_opcode[5];

                let alu_result = case (inst_funct3) matches
                    'b000: begin // ADDI / ADD / SUB
                        let sub = is_reg & inst_funct7[5];
                        if (sub != 0) return truncate(difference);
                        else return x1 + comp_rhs;
                    end
                    'b001: return reverseBits(shifter_out); // SLLI / SLL
                    // SLTI / SLT
                    'b010: return signed_less_than ? 1 : 0;
                    // SLTIU / SLTU
                    'b011: return unsigned_less_than ? 1 : 0;
                    'b100: return x1 ^ comp_rhs; // XORI / XOR
                    'b101: return shifter_out; // SRLI / SRL / SRAI / SRA
                    'b110: return x1 | comp_rhs; // ORI / OR
                    'b111: return x1 & comp_rhs; // ANDI / AND
                endcase;
                regfile.write(inst_rd, alu_result);
            end
            default: begin
                halting = True;
            end
        endcase

        if (halting) state <= onehot_state(HaltState);
        else if (loading) begin
            pc <= next_pc;
            state <= onehot_state(LoadState);
        end else if (storing) begin
            pc <= next_pc;
            state <= onehot_state(JustFetchState);
        end else fetch_next_instruction(next_pc);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule finish_load (is_onehot_state(state, LoadState));
        regfile.write(inst_rd, bus.response);
        fetch_next_instruction(pc);
    endrule

    ///////////////////////////////////////////////////////////////////////////
    // External port connections.

    method OneHotState core_state;
        return state;
    endmethod

    method Word core_inst;
        return inst;
    endmethod

endmodule

endpackage

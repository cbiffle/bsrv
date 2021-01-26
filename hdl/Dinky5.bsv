// Dinky5 is a very simple RISC-V RV32I implementation in Bluespec, designed
// for synthesis on the iCE40 FPGA family.
//
// The intent of this core is to produce the smallest useful RV32I core on an
// iCE40 hx1k (i.e. leaving as many resources as possible available for other
// purposes) without doing anything truly nuts like going bitserial. (Part of
// being useful is having reasonable performance.)
//
// - Not pipelined, though fetch and execute are overlapped; most instructions
//   take 3 cycles, loads and stores take 4.
// - Supports most of RV32I. Currently missing: byte and halfword memory
//   accesses, FENCE, SYSTEM.
// - Halts on unsupported opcodes to simplify debugging.
// - Parameterized address bus / PC width to save space in small SoCs.
// - Minimal bus interface does not support faults or wait states.

package Dinky5;

import BRAMCore::*;
import FShow::*;
import Vector::*;

import Common::*;

///////////////////////////////////////////////////////////////////////////////
// Pseudo-dual-port register file compatible with iCE40 BRAM.
//
// iCE40 BRAM has one dedicated read port and one dedicated write port, while
// Bluespec expects two read/write ports. By only using read on one port and
// write on the other, we can get an equivalent result.
//
// Note that synthesizing this with Yosys requires replacing Bluespec's
// supplied BRAM Verilog with our simplified copy.

interface RegFile;
    // Starts a read of GPR 'index'. The contents will be available after the
    // next clock edge on 'read_result'.
    (* always_ready *)
    method Action read(RegId index);

    // Last value read from a GPR.
    (* always_ready *)
    method Word read_result;

    // Sets register 'index' to 'value'.
    (* always_ready *)
    method Action write(RegId index, Word value);
endinterface

// BRAM-based register file implementation.
(* synthesize *)
module mkRegFile (RegFile);
    BRAM_DUAL_PORT#(RegId, Word) regfile <- mkBRAMCore2Load(valueof(RegCount), False,
        "../hdl/zero-register-set.readmemb", True);

    method Action read(RegId index);
        regfile.a.put(False, index, 0);
    endmethod

    method Action write(RegId index, Word value);
        if (index != 0) regfile.b.put(True, index, value);
    endmethod

    method Word read_result = regfile.a.read;
endmodule

///////////////////////////////////////////////////////////////////////////////
// The Dinky5 CPU Core.

// Core status and debug outputs.
interface Dinky5#(numeric type addr_width);
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
    Reg2State,      // Reading instruction, selecting rs2.
    Reg1State,      // Latching x2, selecting rs1.
    ExecuteState,   // Executing first instruction cycle.
    LoadState,      // Second cycle for loads.
    HaltState       // Something has gone wrong.
} State deriving (Bounded, Bits, FShow, Eq);

instance OneHotIndex#(State, 6);
endinstance
typedef Bit#(6) OneHotState;

module mkDinky5#(DinkyBus#(addr_width) bus) (Dinky5#(addr_width))
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
    // Reg1State!
    Reg#(Word) inst <- mkRegU;
    // Latched second operand (contents addressed by rs2).
    Reg#(Word) x2 <- mkRegU;
    // Latch on input to the magnitude comparator.
    Reg#(Word) comp_rhs <- mkRegU;
    // Our early guess at the next PC value.
    Reg#(Bit#(addr_width)) pc_1 <- mkRegU;

    // General purpose registers.
    RegFile regfile <- mkRegFile;

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
            bus.issue(next_pc, False, 0);
            pc <= next_pc;
            state <= onehot_state(Reg2State);
        endaction;
    endfunction

    // Explain our use of one-hot state encoding to the compiler.
    (* mutually_exclusive = "just_fetch, read_reg_1, read_reg_2, execute, finish_load" *)

    (* fire_when_enabled, no_implicit_conditions *)
    rule just_fetch (is_onehot_state(state, JustFetchState));
        fetch_next_instruction(pc);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule read_reg_2 (is_onehot_state(state, Reg2State));
        inst <= bus.response;
        // Note that in this state, we address the register file directly from
        // the data bus return path -- because we don't have the instruction
        // latched yet! This is the only place where we do this.
        regfile.read(bus.response[24:20]);
        state <= onehot_state(Reg1State);
        pc_1 <= pc + 1;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule read_reg_1 (is_onehot_state(state, Reg1State));
        x2 <= regfile.read_result;
        regfile.read(inst_rs1);
        state <= onehot_state(ExecuteState);

        // Actual cases we want:
        //    'b1100011: return regfile.read_result; // Bxx
        //    'b0110011: return regfile.read_result; // ALU reg
        //    'b0010011: return imm_i; // ALU imm
        // Bluespec does the wrong thing when I literally write that, so let's
        // manually k-map this and notice that it's opcode bit 5 we want.
        //
        // Is this the sort of thing bsc should do? Yes, yes it is.
        comp_rhs <= case (inst_opcode[5]) matches
            'b1: return regfile.read_result; // Bxx, ALU reg
            'b0: return imm_i; // ALU imm
        endcase;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule execute (is_onehot_state(state, ExecuteState));
        let next_pc = pc_1; // we will MUTATE this for jumps!

        let x1 = regfile.read_result;

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
                    default: return True;
                endcase;
                if (condition) next_pc = truncateLSB(pc00 + truncate(imm_b));
            end
            // Lx
            'b0000011: begin
                case (inst_funct3) matches
                    'b010: begin // LW
                        let byte_ea = x1 + imm_i;
                        Bit#(xlen_m2) word_ea = truncateLSB(byte_ea);
                        bus.issue(truncate(word_ea), False, 0);
                        loading = True;
                    end
                    default: halting = True;
                endcase
            end
            // Sx
            'b0100011: begin
                case (inst_funct3) matches
                    'b010: begin // SW
                        let byte_ea = x1 + imm_i;
                        Bit#(xlen_m2) word_ea = truncateLSB(byte_ea);
                        bus.issue(truncate(word_ea), True, x2);
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

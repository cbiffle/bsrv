// Dinky5 is a very simple RISC-V RV32I implementation in Bluespec, designed
// for synthesis on the iCE40 FPGA family.
//
// Dinky5 is old-school and uses between four and five cycles to execute
// instructions.
//
// While Dinky5 is simple, it has some features missing from other simple
// cores, including detection of illegal/unimplemented instructions. (You can't
// do anything useful about such instructions, but they are detected and halt
// the CPU, which makes debugging the CPU easier.)

package Dinky5;

import BRAMCore::*;
import FShow::*;
import Vector::*;

///////////////////////////////////////////////////////////////////////////////
// RISC-V parameters.

// Number of bits in an x register (general purpose register).
typedef 32 XLEN;
// Type held in general purpose registers.
typedef Bit#(XLEN) Word;
// Number of general purpose registers defined.
typedef 32 RegCount;
// Type used to address general purpose registers.
typedef Bit#(TLog#(RegCount)) RegId;

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
    BRAM_DUAL_PORT#(RegId, Word) regfile <- mkBRAMCore2(valueof(RegCount), False);

    method Action read(RegId index);
        regfile.a.put(False, index, ?);
    endmethod

    method Action write(RegId index, Word value);
        regfile.b.put(True, index, value);
    endmethod

    method Word read_result = regfile.a.read;
endmodule

///////////////////////////////////////////////////////////////////////////////
// The Dinky5 CPU Core.

// Dinky5 can be customized in terms of its implemented address bus width. The
// address bus is in terms of _words,_ i.e. the maximum width for XLEN of 32 is
// 30.
//
// Note that Dinky5's bus interface is _synchronous,_ i.e. the result of a read
// is expected on the clock cycle _after_ the address is presented.
//
// This bus interface is aggressively simplified and has no way to report
// faults.
interface Dinky5#(numeric type addr_width);
    // Memory address output to bus. On cycles where memory is not being
    // actively accessed, this output is undefined.
    (* always_ready *)
    method Bit#(addr_width) mem_addr;

    // When 'True', a write is being requested; when 'False', a read.
    (* always_ready *)
    method Bool mem_write;

    // Memory data output to bus, for writes. Undefined during reads.
    (* always_ready *)
    method Word mem_data;
    
    // Memory data return from bus.
    (* always_ready, always_enabled *)
    method Action mem_result(Word value);

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
    ResetState,     // Newly reset.
    FetchState,     // Addressing RAM to fetch instruction.
    Reg2State,      // Reading instruction, selecting rs2.
    Reg1State,      // Latching x2, selecting rs1.
    ExecuteState,   // Executing first instruction cycle.
    LoadState,      // Second cycle for loads.
    HaltState       // Something has gone wrong.
} State deriving (Bits, FShow, Eq);

// One-hot representation of State; must have one bit for each enum
// discriminant.
typedef Bit#(7) OneHotState;

// Converts from weighted to one-hot representation.
function OneHotState onehot_state(State s);
    return 1 << pack(s);
endfunction

// Checks a bit in the one-hot state.
function Bool is_onehot_state(OneHotState oh, State s);
    return oh[pack(s)] != 0;
endfunction

module mkDinky5 (Dinky5#(addr_width))
provisos (
    // XLEN is >= 2
    Add#(xlen_m2, 2, XLEN),
    // addr_width is <= XLEN-2
    Add#(addr_width, dropped_addr_msbs, xlen_m2)
);
    ///////////////////////////////////////////////////////////////////////////
    // State elements.

    // State of execution state machine.
    Reg#(OneHotState) state <- mkReg(onehot_state(ResetState));
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

    // General purpose registers.
    RegFile regfile <- mkRegFile;

    ///////////////////////////////////////////////////////////////////////////
    // Internal buses and combinational circuits.

    // Path from address generation to bus port.
    Wire#(Bit#(addr_width)) mem_addr_port <- mkDWire(?);
    // Path from write signal to bus port.
    PulseWire mem_write_port <- mkPulseWire;
    // Path from datapath to bus port for writes.
    Wire#(Word) mem_data_port <- mkDWire(?);
    // Path from bus return to datapath for reads.
    Wire#(Word) mem_result_port <- mkBypassWire;

    // PC extended as a byte address, which is the version RISC-V instructions
    // want to use for arithmetic.
    let pc00 = {pc, 2'b00};

    // Instruction fields.
    let inst_opcode = inst[6:0];
    let inst_rd = inst[11:7];
    let inst_funct3 = inst[14:12];
    let inst_rs1 = inst[19:15];
    let inst_funct7 = inst[31:25];

    ///////////////////////////////////////////////////////////////////////////
    // Core execution rules.

    // Explain our use of one-hot state encoding to the compiler.
    (* mutually_exclusive = "leave_reset, fetch, read_reg_1, read_reg_2, execute, finish_load" *)

    (* fire_when_enabled, no_implicit_conditions *)
    rule leave_reset (is_onehot_state(state, ResetState));
        state <= onehot_state(FetchState);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule fetch (is_onehot_state(state, FetchState));
        state <= onehot_state(Reg2State);
        mem_addr_port <= pc;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule read_reg_2 (is_onehot_state(state, Reg2State));
        inst <= mem_result_port;
        // Note that in this state, we address the register file directly from
        // the data bus return path -- because we don't have the instruction
        // latched yet! This is the only place where we do this.
        regfile.read(mem_result_port[24:20]);
        state <= onehot_state(Reg1State);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule read_reg_1 (is_onehot_state(state, Reg1State));
        let imm_i = signExtend(inst[31:20]);

        x2 <= regfile.read_result;
        regfile.read(inst_rs1);
        state <= onehot_state(ExecuteState);

        comp_rhs <= case (inst_opcode) matches
            'b1100011: return regfile.read_result; // Bxx
            'b0110011: return regfile.read_result; // ALU reg
            'b0010011: return imm_i; // ALU imm
            default: return ?;
        endcase;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule execute (is_onehot_state(state, ExecuteState));
        let next_pc = pc + 1; // we will MUTATE this for jumps!

        // Various immediate decodes
        Word imm_i = signExtend(inst[31:20]);
        Word imm_u = {inst[31:12], 0};
        Word imm_j = {
            signExtend(inst[31]), inst[19:12], inst[20], inst[30:21], 1'b0};
        Word imm_b = {
            signExtend(inst[31]), inst[7], inst[30:25], inst[11:8], 1'b0};

        let x1 = regfile.read_result;

        let signed_less_than = toSigned(x1) < toSigned(comp_rhs);
        let unsigned_less_than = x1 < comp_rhs;

        // Behold, the Big Fricking RV32I Case Discriminator!
        case (inst_opcode) matches
            // LUI
            'b0110111: begin
                regfile.write(inst_rd, imm_u);
                state <= onehot_state(FetchState);
            end
            // AUIPC
            'b0010111: begin
                regfile.write(inst_rd, extend(pc00 + truncate(imm_u)));
                state <= onehot_state(FetchState);
            end
            // JAL
            'b1101111: begin
                regfile.write(inst_rd, extend(pc00));
                next_pc = truncateLSB(pc00 + truncate(imm_j));
                state <= onehot_state(FetchState);
            end
            // JALR
            'b1100111: begin
                regfile.write(inst_rd, extend(pc00));
                Word full_ea = x1 + imm_i;
                Bit#(xlen_m2) word_ea = truncateLSB(full_ea);
                next_pc = truncate(word_ea);
                state <= onehot_state(FetchState);
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
                state <= onehot_state(FetchState);
            end
            // Lx
            'b0000011: begin
                case (inst_funct3) matches
                    'b010: begin // LW
                        let byte_ea = x1 + imm_i;
                        Bit#(xlen_m2) word_ea = truncateLSB(byte_ea);
                        mem_addr_port <= truncate(word_ea);
                        state <= onehot_state(LoadState);
                    end
                    default: state <= onehot_state(HaltState);
                endcase
            end
            // Sx
            'b0100011: begin
                case (inst_funct3) matches
                    'b010: begin // SW
                        let byte_ea = x1 + imm_i;
                        Bit#(xlen_m2) word_ea = truncateLSB(byte_ea);
                        mem_addr_port <= truncate(word_ea);
                        mem_data_port <= x2;
                        mem_write_port.send;
                        state <= onehot_state(FetchState);
                    end
                    default: state <= onehot_state(HaltState);
                endcase
            end
            // ALU immediate
            'b0010011: begin
                let alu_result = case (inst_funct3) matches
                    'b000: return x1 + imm_i; // ADDI
                    'b001: return x1 << comp_rhs[4:0]; // SLLI
                    // SLTI
                    'b010: return signed_less_than ? 1 : 0;
                    // SLTIU
                    'b011: return unsigned_less_than ? 1 : 0;
                    'b100: return x1 ^ comp_rhs; // XORI
                    'b101: if (inst_funct7[5] == 0) begin // SRLI
                        return x1 >> comp_rhs[4:0];
                    end else begin // SRAI
                        return pack(toSigned(x1) >> comp_rhs[4:0]);
                    end
                    'b110: return x1 | comp_rhs;
                    'b111: return x1 & comp_rhs;
                endcase;
                regfile.write(inst_rd, alu_result);
                state <= onehot_state(FetchState);
            end
            // ALU reg
            'b0110011: begin
                let alu_result = case (inst_funct3) matches
                    'b000: begin
                        let sub = inst_funct7[5];
                        return x1 + (x2 ^ signExtend(sub)) + zeroExtend(sub);
                    end
                    'b001: return x1 << comp_rhs[4:0]; // SLL
                    // SLT
                    'b010: return signed_less_than ? 1 : 0;
                    // SLTU
                    'b011: return unsigned_less_than ? 1 : 0;
                    'b100: return x1 ^ comp_rhs; // XOR
                    'b101: if (inst_funct7[5] == 0) begin // SRL
                        return x1 >> comp_rhs[4:0];
                    end else begin // SRA
                        return pack(toSigned(x1) >> comp_rhs[4:0]);
                    end
                    'b110: return x1 | comp_rhs;
                    'b111: return x1 & comp_rhs;
                endcase;
                regfile.write(inst_rd, alu_result);
                state <= onehot_state(FetchState);
            end
            default: begin
                state <= onehot_state(HaltState);
            end
        endcase

        pc <= next_pc;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule finish_load (is_onehot_state(state, LoadState));
        regfile.write(inst_rd, mem_result_port);
        state <= onehot_state(FetchState);
    endrule

    ///////////////////////////////////////////////////////////////////////////
    // External port connections.

    method Bit#(addr_width) mem_addr = mem_addr_port;
    method Bool mem_write = mem_write_port;
    method Word mem_data = mem_data_port;

    method Action mem_result(Word value);
        mem_result_port <= value;
    endmethod

    method OneHotState core_state;
        return state;
    endmethod

    method Word core_inst;
        return inst;
    endmethod

endmodule

///////////////////////////////////////////////////////////////////////////////
// Utility stuff.

// Convenient concrete synthesis target with a 16-bit byte address space
// (14-bit external bus). This is useful for getting Verilog of just the CPU
// while debuggint the CPU.
(* synthesize *)
module mkDinky5_14 (Dinky5#(14));
    Dinky5#(14) core <- mkDinky5;
    return core;
endmodule

// Rough equivalent of Verilog 'signed' function. Useful for forcing sign
// extension in shifts.
function Int#(XLEN) toSigned(Word x);
    return unpack(x);
endfunction

endpackage

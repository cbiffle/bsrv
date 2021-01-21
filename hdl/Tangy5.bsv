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
// 2R1W register file designed around iCE40 pseudo-dual-port block RAM.
//
// iCE40 BRAM has one dedicated read port and one dedicated write port, while
// Bluespec's BRAM modules expect two read/write ports (as on Xilinx). By only
// using read on one port and write on the other, we can get an equivalent
// result.
//
// To get two read ports, we duplicate the BRAM, reading from each copy
// separately but writing to both.
//
// Note that synthesizing this with Yosys requires replacing Bluespec's
// supplied BRAM Verilog with our simplified copy.

interface RegFile;
    // Starts a read of GPRs 'rs1' and 'rs2'. The contents will be available
    // after the next clock edge on 'read_result'.
    (* always_ready *)
    method Action read(RegId rs1, RegId rs2);

    // Last values read from GPRs.
    (* always_ready *)
    method Tuple2#(Word, Word) read_result;

    // Sets register 'index' to 'value'.
    (* always_ready *)
    method Action write(RegId index, Word value);
endinterface

// BRAM-based register file implementation.
(* synthesize *)
module mkRegFile (RegFile);
    BRAM_DUAL_PORT#(RegId, Word) rf0 <- mkBRAMCore2(valueof(RegCount), False);
    BRAM_DUAL_PORT#(RegId, Word) rf1 <- mkBRAMCore2(valueof(RegCount), False);

    method Action read(RegId rs1, RegId rs2);
        rf0.a.put(False, rs1, ?);
        rf1.a.put(False, rs2, ?);
    endmethod

    method Action write(RegId index, Word value);
        rf0.b.put(True, index, value);
        rf1.b.put(True, index, value);
    endmethod

    method Tuple2#(Word, Word) read_result = tuple2(rf0.a.read, rf1.a.read);
endmodule

///////////////////////////////////////////////////////////////////////////////
// The Tangy5 CPU Core.

// Tangy5 can be customized in terms of its implemented address bus width. The
// address bus is in terms of _words,_ i.e. the maximum width for XLEN of 32 is
// 30.
//
// Note that Tangy5's bus interface is _synchronous,_ i.e. the result of a read
// is expected on the clock cycle _after_ the address is presented.
//
// This bus interface is aggressively simplified and has no way to report
// faults.
interface Tangy5#(numeric type addr_width);
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
    JustFetchState, // Reset, or second cycle of store.
    RegState,       // Reading instruction, selecting registers.
    ExecuteState,   // Executing first instruction cycle.
    LoadState,      // Second cycle for loads.
    HaltState       // Something has gone wrong.
} State deriving (Bits, FShow, Eq);

// One-hot representation of State; must have one bit for each enum
// discriminant.
typedef Bit#(5) OneHotState;

// Converts from weighted to one-hot representation.
function OneHotState onehot_state(State s);
    return 1 << pack(s);
endfunction

// Checks a bit in the one-hot state.
function Bool is_onehot_state(OneHotState oh, State s);
    return oh[pack(s)] != 0;
endfunction

module mkTangy5 (Tangy5#(addr_width))
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
            mem_addr_port <= next_pc;
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
        inst <= mem_result_port;
        // Note that in this state, we address the register file directly from
        // the data bus return path -- because we don't have the instruction
        // latched yet!
        regfile.read(mem_result_port[19:15], mem_result_port[24:20]);
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

        let signed_less_than = toSigned(x1) < toSigned(comp_rhs);
        let unsigned_less_than = x1 < comp_rhs;

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
                regfile.write(inst_rd, extend(pc00 + truncate(imm_u)));
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
                        mem_addr_port <= truncate(word_ea);
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
                        mem_addr_port <= truncate(word_ea);
                        mem_data_port <= x2;
                        mem_write_port.send;
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
                        return x1 + (comp_rhs ^ signExtend(sub))
                                  + zeroExtend(sub);
                    end
                    'b001: return x1 << comp_rhs[4:0]; // SLLI / SLL
                    // SLTI / SLT
                    'b010: return signed_less_than ? 1 : 0;
                    // SLTIU / SLTU
                    'b011: return unsigned_less_than ? 1 : 0;
                    'b100: return x1 ^ comp_rhs; // XORI / XOR
                    'b101: if (inst_funct7[5] == 0) begin // SRLI / SRL
                        return x1 >> comp_rhs[4:0];
                    end else begin // SRAI / SRA
                        return pack(toSigned(x1) >> comp_rhs[4:0]);
                    end
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
        regfile.write(inst_rd, mem_result_port);
        fetch_next_instruction(pc);
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
module mkTangy5_14 (Tangy5#(14));
    Tangy5#(14) core <- mkTangy5;
    return core;
endmodule

// Rough equivalent of Verilog 'signed' function. Useful for forcing sign
// extension in shifts.
function Int#(XLEN) toSigned(Word x);
    return unpack(x);
endfunction

endpackage

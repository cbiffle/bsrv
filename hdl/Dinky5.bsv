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
    (* always_ready *)
    method Action mem_result(Word value);

    // Internal state of core, for debugging.
    (* always_ready *)
    method State core_state;

    // Currently latched instruction, for debugging.
    (* always_ready *)
    method Word core_inst;
endinterface

// Execution states of the CPU.
typedef enum {
    ResetState,     // Newly reset.
    FetchState,     // Addressing RAM to fetch instruction.
    Reg1State,      // Reading instruction, selecting rs1.
    Reg2State,      // Selecting rs2.
    ExecuteState,   // Executing first instruction cycle.
    LoadState,      // Second cycle for loads.
    HaltState       // Something has gone wrong.
} State deriving (Bits, FShow, Eq);

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
    Reg#(State) state <- mkReg(ResetState);
    // Address of current instruction. Note that this is a word address, not a
    // byte address, so it is missing its two LSBs.
    Reg#(Bit#(addr_width)) pc <- mkReg(0);
    // Latched instruction being executed -- only valid in states past
    // Reg1State!
    Reg#(Word) inst <- mkRegU;
    // Latched first operand (contents addressed by rs1).
    Reg#(Word) x1 <- mkRegU;

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
    Wire#(Word) mem_result_port <- mkWire;

    // Addressing signals for register file read port.
    Wire#(RegId) rf_rs <- mkWire;
    // Return bus for register contents.
    Wire#(Word) rf_result <- mkBypassWire;
    // Addressing signals for register file write port.
    Wire#(Tuple2#(RegId, Word)) rf_wr <- mkWire;

    // PC extended as a byte address, which is the version RISC-V instructions
    // want to use for arithmetic.
    let pc00 = {pc, 2'b00};

    ///////////////////////////////////////////////////////////////////////////
    // RegFile operation rules.

    (* fire_when_enabled *)
    rule regfile_read_1;
        regfile.read(rf_rs);
    endrule

    (* fire_when_enabled *)
    rule regfile_read_2;
        rf_result <= regfile.read_result;
    endrule

    (* fire_when_enabled *)
    rule regfile_write (rf_wr matches {.rd, .value});
        $display("RF WRITE x%0d <= %0h", rd, value);
        if (rd != 0) regfile.write(rd, value);
    endrule

    ///////////////////////////////////////////////////////////////////////////
    // Core execution rules.

    (* fire_when_enabled, no_implicit_conditions *)
    rule leave_reset (state matches ResetState);
        state <= FetchState;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule fetch (state matches FetchState);
        state <= Reg1State;
        mem_addr_port <= pc;
    endrule

    // Implicit condition: mem result port valid
    (* fire_when_enabled *)
    rule read_reg_1 (state matches Reg1State);
        inst <= mem_result_port;
        rf_rs <= mem_result_port[19:15];
        state <= Reg2State;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule read_reg_2 (state matches Reg2State);
        x1 <= rf_result;
        rf_rs <= inst[24:20];
        state <= ExecuteState;
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule execute (state matches ExecuteState);
        let opcode = inst[6:0];
        let funct3 = inst[14:12];
        let funct7 = inst[31:25];
        let rd = inst[11:7];

        let next_pc = pc + 1;

        Word imm_i = signExtend(inst[31:20]);
        Word imm_u = {inst[31:12], 0};
        Word imm_j = {
            signExtend(inst[31]), inst[19:12], inst[20], inst[30:21], 1'b0};
        Word imm_b = {
            signExtend(inst[31]), inst[7], inst[30:25], inst[11:8], 1'b0};

        // Behold, the Big Fricking RV32I Case Discriminator!
        case (opcode) matches
            // LUI
            'b0110111: begin
                rf_wr <= tuple2(rd, imm_u);
                state <= FetchState;
            end
            // AUIPC
            'b0010111: begin
                rf_wr <= tuple2(rd, extend(pc00) + imm_u);
                state <= FetchState;
            end
            // JAL
            'b1101111: begin
                rf_wr <= tuple2(rd, extend(pc00));
                next_pc = truncateLSB(pc00 + truncate(imm_j));
                state <= FetchState;
            end
            // JALR
            'b1100111: begin
                rf_wr <= tuple2(rd, extend(pc00));
                Word full_ea = x1 + imm_i;
                Bit#(xlen_m2) word_ea = truncateLSB(full_ea);
                next_pc = truncate(word_ea);
                state <= FetchState;
            end
            // Bxx
            'b1100011: begin
                let condition = case (funct3) matches
                    'b000: return x1 == rf_result;
                    'b001: return x1 != rf_result;
                    'b100: return toSigned(x1) < toSigned(rf_result);
                    'b101: return toSigned(x1) >= toSigned(rf_result);
                    'b110: return x1 < rf_result;
                    'b111: return x1 >= rf_result;
                    default: return ?;
                endcase;
                if (condition) next_pc = truncateLSB(pc00 + truncate(imm_b));
                state <= FetchState;
            end
            // Lx
            'b0000011: begin
                case (funct3) matches
                    'b010: begin // LW
                        let byte_ea = x1 + imm_i;
                        Bit#(xlen_m2) word_ea = truncateLSB(byte_ea);
                        mem_addr_port <= truncate(word_ea);
                        state <= LoadState;
                    end
                    default: state <= HaltState;
                endcase
            end
            // Sx
            'b0100011: begin
                case (funct3) matches
                    'b010: begin // SW
                        let byte_ea = x1 + imm_i;
                        Bit#(xlen_m2) word_ea = truncateLSB(byte_ea);
                        mem_addr_port <= truncate(word_ea);
                        mem_data_port <= rf_result;
                        mem_write_port.send;
                        state <= FetchState;
                    end
                    default: state <= HaltState;
                endcase
            end
            // ALU immediate
            'b0010011: begin
                let alu_result = case (funct3) matches
                    'b000: return x1 + imm_i; // ADDI
                    'b001: return x1 << imm_i[4:0]; // SLLI
                    // SLTI
                    'b010: return toSigned(x1) < toSigned(imm_i) ? 1 : 0;
                    // SLTIU
                    'b011: return x1 < imm_i ? 1 : 0;
                    'b100: return x1 ^ imm_i; // XORI
                    'b101: if (funct7[5] == 0) begin // SRLI
                        return x1 >> imm_i[4:0];
                    end else begin // SRAI
                        return pack(toSigned(x1) >> imm_i[4:0]);
                    end
                    'b110: return x1 | imm_i;
                    'b111: return x1 & imm_i;
                endcase;
                rf_wr <= tuple2(rd, alu_result);
                state <= FetchState;
            end
            // ALU reg
            'b0110011: begin
                let alu_result = case (funct3) matches
                    'b000: begin
                        let sub = funct7[5];
                        return x1 + (rf_result ^ signExtend(sub)) + zeroExtend(sub);
                    end
                    'b001: return x1 << rf_result[4:0]; // SLL
                    // SLT
                    'b010: return toSigned(x1) < toSigned(rf_result) ? 1 : 0;
                    // SLTU
                    'b011: return x1 < rf_result ? 1 : 0;
                    'b100: return x1 ^ rf_result; // XOR
                    'b101: if (funct7[5] == 0) begin // SRL
                        return x1 >> rf_result[4:0];
                    end else begin // SRA
                        return pack(toSigned(x1) >> rf_result[4:0]);
                    end
                    'b110: return x1 | rf_result;
                    'b111: return x1 & rf_result;
                endcase;
                rf_wr <= tuple2(rd, alu_result);
                state <= FetchState;
            end
            default: begin
                state <= HaltState;
            end
        endcase

        pc <= next_pc;
    endrule

    // Implicit condition: mem result port valid
    (* fire_when_enabled *)
    rule finish_load (state matches LoadState);
        let rd = inst[11:7];
        rf_wr <= tuple2(rd, mem_result_port);
        state <= FetchState;
    endrule

    ///////////////////////////////////////////////////////////////////////////
    // External port connections.

    method Bit#(addr_width) mem_addr = mem_addr_port;
    method Bool mem_write = mem_write_port;
    method Word mem_data = mem_data_port;

    method Action mem_result(Word value);
        mem_result_port <= value;
    endmethod

    method State core_state;
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

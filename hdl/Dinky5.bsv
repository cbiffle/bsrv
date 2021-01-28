// Dinky5 is a very simple RISC-V RV32I implementation in Bluespec, designed
// for synthesis on the iCE40 FPGA family.
//
// The intent of this core is to produce the smallest useful RV32I core on an
// iCE40 hx1k (i.e. leaving as many resources as possible available for other
// purposes) without doing anything truly nuts like going bitserial. (Part of
// being useful is having reasonable performance.)
//
// - Not pipelined, though fetch and execute are overlapped.
// - Most instructions take 3 cycles.
// - Loads and stores, 4.
// - Does not include a barrel shifter, for area reasons, so shifts take 3 +
//   number of positions shifted.
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
    ShiftState,     // Processing a serial shift operation.
    HaltState       // Something has gone wrong.
} State deriving (Bounded, Bits, FShow, Eq);

instance OneHotIndex#(State, 7);
endinstance
typedef Bit#(7) OneHotState;

module mkDinky5#(DinkyBus#(addr_width) bus) (Dinky5#(addr_width))
provisos (
    // XLEN is >= 2
    Add#(xlen_m2, 2, XLEN),
    // addr_width is <= XLEN-2
    Add#(addr_width, dropped_addr_msbs, xlen_m2)
);
    // Crops a Word value for use as a smaller word address of addr_width bits.
    function Bit#(addr_width) crop_addr(Word addr);
        Bit#(xlen_m2) div4 = truncateLSB(addr);
        return truncate(div4);
    endfunction

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
    // Shifter state: number of bits remaining to shift.
    Reg#(Bit#(5)) shift_amt <- mkRegU;
    // Shifter state: bit that will be shifted in on right-shift.
    Reg#(bit) shift_fill <- mkRegU;
    // Record of load effective address LSBs for use in shifting the returned
    // value into place.
    Reg#(Bit#(2)) load_lsbs <- mkRegU;

    // General purpose registers.
    RegFile1 regfile <- mkRegFile1;

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
            bus.issue(next_pc, 4'b0000, 0);
            pc <= next_pc;
            state <= onehot_state(Reg2State);
        endaction;
    endfunction

    // Explain our use of one-hot state encoding to the compiler.
    (* mutually_exclusive = "just_fetch, read_reg_1, read_reg_2, execute, finish_load, keep_shifting" *)

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
        let next_pc = pc + 1; // we will MUTATE this for jumps!

        let x1 = regfile.read_result;

        // Force structural sharing between the subtraction circuit and the
        // comparators.
        let difference = zeroExtend(x1) + {1'b1, ~comp_rhs} + 1;
        let signed_less_than = unpack(
            (x1[31] ^ comp_rhs[31]) != 0 ? x1[31] : difference[32]);
        let unsigned_less_than = unpack(difference[32]);

        // Behold, the Big Fricking RV32I Case Discriminator!
        let halting = False;
        let shifting = False;
        let loading = False;
        let storing = False;
        case (inst_opcode) matches
            // LUI
            'b0110111: regfile.write(inst_rd, imm_u);
            // AUIPC
            'b0010111: regfile.write(inst_rd, extend(pc00) + imm_u);
            // JAL
            'b1101111: begin
                regfile.write(inst_rd, extend({pc + 1, 2'b00}));
                next_pc = crop_addr(extend(pc00) + imm_j);
            end
            // JALR
            'b1100111: begin
                regfile.write(inst_rd, extend({pc + 1, 2'b00}));
                next_pc = crop_addr(x1 + imm_i);
            end
            // Bxx
            'b1100011: begin
                let condition = case (inst_funct3) matches
                    'b000: return x1 == x2;
                    'b001: return x1 != x2;
                    'b100: return signed_less_than;
                    'b101: return !signed_less_than;
                    // We're folding in the two undefined condition codes here
                    // for a logic simplification. This is the sort of thing I'd
                    // expect my toolchain to figure out for me given an omitted
                    // or explicitly undefined default case, but it doesn't.
                    'b?10: return unsigned_less_than;
                    'b?11: return !unsigned_less_than;
                endcase;
                if (condition) next_pc = crop_addr(extend(pc00) + imm_b);
            end
            // Lx
            'b0000011: begin
                let ea = x1 + imm_i;
                load_lsbs <= ea[1:0];
                // We'll go ahead and issue the load even if it's not aligned
                // correctly, to reduce logic here.
                bus.issue(crop_addr(ea), 4'b0000, 0);
                // Misalignment check
                let aligned = case (inst_funct3) matches
                    'b010: is_aligned(ea, 2); // LW
                    'b?00: True; // LB / LBU
                    'b?01: is_aligned(ea, 1); // LH/LHU
                    default: False; // 64-bit operation
                endcase;
                loading = True;
                halting = !aligned;
            end
            // Sx
            'b0100011: begin
                let ea = x1 + imm_s;
                // The alignment check will serve as our guard against both
                // unaligned stores, _and_ illegal size encodings. If aligned
                // is not set, the store will be blunted.
                let aligned = case (inst_funct3) matches
                    'b000: True;
                    'b001: (ea[0] == 0);
                    'b010: (ea[1:0] == 0);
                    default: False;
                endcase;
                let mask = case (inst_funct3) matches
                    'b000: 1 << ea[1:0];
                    'b001: 'b11 << ea[1:0];
                    'b010: 'b1111;
                endcase;
                let val = case (inst_funct3) matches
                    'b000: {x2[7:0], x2[7:0], x2[7:0], x2[7:0]};
                    'b001: {x2[15:0], x2[15:0]};
                    'b010: x2;
                endcase;
                bus.issue(crop_addr(ea), aligned ? mask : 0, val);
                storing = True;
                halting = !aligned;
            end
            // ALU reg/immediate
            'b0?10011: begin
                let is_reg = inst_opcode[5];

                let alu_result = 0;
                case (inst_funct3) matches
                    'b000: begin // ADDI / ADD / SUB
                        let sub = is_reg & inst_funct7[5];
                        if (sub != 0) alu_result = truncate(difference);
                        else alu_result = x1 + comp_rhs;
                    end
                    'b001: begin // SLLI / SLL
                        shifting = True;
                        shift_fill <= 0;
                        shift_amt <= comp_rhs[4:0];
                        x2 <= x1;
                    end
                    // SLTI / SLT
                    'b010: alu_result = signed_less_than ? 1 : 0;
                    // SLTIU / SLTU
                    'b011: alu_result = unsigned_less_than ? 1 : 0;
                    'b100: alu_result = x1 ^ comp_rhs; // XORI / XOR
                    'b101: begin // SRLI / SRL / SRAI / SRA
                        shifting = True;
                        shift_fill <= x1[31] & inst_funct7[5];
                        shift_amt <= comp_rhs[4:0];
                        x2 <= x1;
                    end
                    'b110: alu_result = x1 | comp_rhs; // ORI / OR
                    'b111: alu_result = x1 & comp_rhs; // ANDI / AND
                endcase
                regfile.write(inst_rd, alu_result);
            end
            default: begin
                halting = True;
            end
        endcase

        if (halting) state <= onehot_state(HaltState);
        else if (shifting) begin
            pc <= next_pc;
            state <= onehot_state(ShiftState);
        end else if (loading) begin
            pc <= next_pc;
            state <= onehot_state(LoadState);
        end else if (storing) begin
            pc <= next_pc;
            state <= onehot_state(JustFetchState);
        end else fetch_next_instruction(next_pc);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule keep_shifting (is_onehot_state(state, ShiftState));
        let right = inst_funct3[2];

        regfile.write(inst_rd, x2);

        if (shift_amt == 0) begin
            fetch_next_instruction(pc);
            // Make it clear that we don't need to gate shift_amt updates by
            // this condition; this is a case where ? doesn't confuse bsc
            shift_amt <= ?;
        end else if (right == 1) begin
            x2 <= {shift_fill, truncateLSB(x2)};
            shift_amt <= shift_amt - 1;
        end else begin // left
            x2 <= {truncate(x2), 1'b0};
            shift_amt <= shift_amt - 1;
        end
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule finish_load (is_onehot_state(state, LoadState));
        let size = inst_funct3[1:0];
        let zext = inst_funct3[2] == 1;

        // I am delighted to report that Yosys produces a circuit just as
        // compact as my handrolled alternative in response to this shift, so
        // there is no need to complicate things.
        let shifted = bus.response >> {load_lsbs, 3'b0};

        regfile.write(inst_rd, case (size) matches
            'b00: begin
                let b = shifted[7:0];
                return zext ? extend(b) : signExtend(b);
            end
            'b01: begin
                let h = shifted[15:0];
                return zext ? extend(h) : signExtend(h);
            end
            'b10: bus.response;
        endcase);
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

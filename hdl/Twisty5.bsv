// Twisty5 is an attempt at squeezing a lot of RISC-V performance out of a
// cheap FPGA through hardware multithreading.
//
// This is the result of three observations:
// 1. iCE40 BRAM primitives are just about 4x larger than we need for RV32I.
// 2. High clock rates mean small pipeline stages, which in a single-thread
//    processor mean deep pipelines and bypass circuits. Bypass circuits are
//    relatively expensive on FPGAs because of the wide muxes they place on the
//    critical path and the routing resources they consume.
// 3. Concurrency is awesome.
//
// Twisty5 always runs four threads. It also has a four-stage pipeline. This is
// not a coincidence: each thread "occupies" a single pipeline stage at any
// given time, and only one instruction from a given thread is executing at any
// time.
//
// You can think of the system as alternating between threads at each clock
// cycle. Each thread takes 4 system clock cycles to execute most instructions,
// so at 80MHz system clock each thread runs at 20MIPS. (Load and store
// operations take twice as long due to bus contention.)

package Twisty5;

import BRAMCore::*;
import Connectable::*;
import GetPut::*;
import UniqueWrappers::*;
import Vector::*;

import Common::*;

///////////////////////////////////////////////////////////////////////////////
// System parameters and interfaces.

// Number of hardware threads. "Hart" is RISC-V jargon.
typedef 4 HartCount;
// Enough bits to distinguish all the harts.
typedef Bit#(TLog#(HartCount)) HartId;

// Interface that we expect to be implemented by the bus fabric.
interface TwistyBus#(numeric type addr_width);
    // Issues a transaction to the bus. If any of the lanes in `write_data` is
    // `Valid` this is a write, otherwise it's a read.
    (* always_ready *)
    method Action issue(
        Bit#(addr_width) address,
        Vector#(4, Maybe#(Bit#(8))) write_data);
    // Data from a read request issued on the previous cycle; undefined
    // otherwise.
    (* always_ready *)
    method Word response;
endinterface

// Interface exposed by the core. These are mostly debug signals, the core
// mostly communicates with the outside world through the bus fabric.
interface Twisty5#(numeric type addr_width);
    (* always_ready *)
    method Bool halted;
    (* always_ready *)
    method HartId next_hart_id;
    (* always_ready *)
    method HartState next_hart_state;
endinterface

///////////////////////////////////////////////////////////////////////////////
// Internal state.

// Execution state for a hart.
typedef union tagged {
    // An instruction needs fetched before we can do anything. This happens
    // both at reset, but also as the second cycle of a store.
    void ResetState;
    // An instruction is in cache and we're good to go.
    void RunState;
    // We're doing the second cycle of a load.
    struct {
        // Register where the loaded data is deposited.
        RegId rd;
        // The two bottom bits of the effective address, recorded to help us
        // place byte/halfword quantities into the right bits of the register.
        Bit#(2) lsbs;
        // The f3 field from the instruction, giving us the transaction size
        // and sign/zero extension.
        Bit#(3) saved_funct3;
    } LoadState;
    // Something invalid happened and we are parked.
    void HaltState;
} HartState deriving (Bits, FShow);

typedef enum { Left, Right } ShiftDir deriving (Bits, FShow);

// State needed by a hart in every stage of the pipeline.
typedef struct {
    // Who are we?
    HartId hart;
    // Where are we?
    Bit#(addr_width) pc;
    // What are we doing?
    HartState state;
} CoreState#(numeric type addr_width) deriving (Bits, FShow);

///////////////////////////////////////////////////////////////////////////////
// Pipeline register contents.

// Data on stage 1's input register.
typedef struct {
    CoreState#(addr_width) cs;
    // Cached result of last memory read, often an instruction but sometimes
    // data - depends on the execution state.
    Word cache;
} Stage1#(numeric type addr_width) deriving (Bits, FShow);

// Data on stage 2's input register.
typedef struct {
    CoreState#(addr_width) cs;
    // Cached result of last memory read, forwarded from stage1.
    Word cache;
} Stage2#(numeric type addr_width) deriving (Bits, FShow);

// Data on stage 3's input register.
typedef struct {
    CoreState#(addr_width) cs;
    // Cached result of last memory read, forwarded from stage2.
    Word cache;
    // Value of register addressed by rs1 field.
    Word x1;
    // Value of register addressed by rs2 field.
    Word x2;
    // Result of bottom section of comparator chain.
    Bit#(25) diff_lo;
    // Record of the value used on the right hand side of the comparator.
    Word rhs;
} Stage3#(numeric type addr_width) deriving (Bits, FShow);

// Data on stage 4's input register.
typedef struct {
    CoreState#(addr_width) cs;
    // If Valid, gives the register and data to write to the register file.
    Maybe#(Tuple2#(RegId, Word)) rf_write;
} Stage4#(numeric type addr_width) deriving (Bits, FShow);

///////////////////////////////////////////////////////////////////////////////
// Implementation

module mkTwisty5#(
    TwistyBus#(addr_width) bus
) (Twisty5#(addr_width))
provisos (
    // XLEN is >= 2
    Add#(xlen_m2, 2, XLEN),
    // addr_width is <= XLEN-2
    Add#(addr_width, dropped_addr_msbs, xlen_m2)
);
    // The big shared regfile.
    RegFile2H regfile <- mkRegFile2H;

    // Pipeline. We initialize the register at each pipeline stage to set all
    // four harts to ResetState, each PC to the appropriate reset vector, and
    // hart 0 ready to go in stage 3 so it will fetch first.
    Pipe#(Stage1#(addr_width), Stage2#(addr_width)) s1mod <-
        mkStage1(regfile, Stage1
            { cs: CoreState
                { hart: 2
                , pc: 2 * 2
                , state: tagged ResetState
                }
            , cache: 0
            });
    Pipe#(Stage2#(addr_width), Stage3#(addr_width)) s2mod <-
        mkStage2(regfile, Stage2
            { cs: CoreState
                { hart: 1
                , pc: 1 * 2
                , state: tagged ResetState
                }
            , cache: 0
            });
    Pipe#(Stage3#(addr_width), Stage4#(addr_width)) s3mod <-
        mkStage3(bus, Stage3
            { cs: CoreState
                { hart: 0
                , pc: 0 * 2
                , state: tagged ResetState
                }
            , cache: 0
            , x1: 0
            , x2: 0
            , diff_lo: 0
            , rhs: 0
            });
    Pipe#(Stage4#(addr_width), Stage1#(addr_width)) s4mod <-
        mkStage4(regfile, bus, Stage4
            { cs: CoreState
                { hart: 3
                , pc: 3 * 2
                , state: tagged ResetState
                }
            , rf_write: tagged Invalid
            });

    mkConnection(s1mod.out, s2mod.feed);
    mkConnection(s2mod.out, s3mod.feed);
    mkConnection(s3mod.out, s4mod.feed);
    mkConnection(s4mod.out, s1mod.feed);

    // Diagnostic outputs
    method HartId next_hart_id = s3mod.state.cs.hart;
    method HartState next_hart_state = s3mod.state.cs.state;
    method Bool halted = s3mod.state.cs.state matches tagged HaltState ? True : False;
endmodule

///////////////////////////////////////////////////////////////////////////////
// Generic pipeline module interface

(* always_ready, always_enabled *)
interface Pipe#(type i, type o);
    interface Put#(i) feed;
    interface Get#(o) out;

    method i state;
endinterface

///////////////////////////////////////////////////////////////////////////////
// Stage 1 module

module mkStage1#(
    RegFile2H regfile,
    Stage1#(aw) start_state
) (Pipe#(Stage1#(aw), Stage2#(aw)));
    let s <- mkReg(start_state);
    let stage2 <- mkBypassWire;

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage_1;
        InstFields fields = unpack(s.cache);
        regfile.read(s.cs.hart, fields.rs1, fields.rs2);
        stage2 <= Stage2
            { cs: s.cs
            , cache: s.cache
            };
    endrule

    interface Put feed = toPut(asReg(s));
    interface Get out = wireGet(stage2);
    method state = s;
endmodule

///////////////////////////////////////////////////////////////////////////////
// Stage 2 module

module mkStage2#(
    RegFile2H regfile,
    Stage2#(aw) start_state
) (Pipe#(Stage2#(aw), Stage3#(aw)));
    let s <- mkReg(start_state);
    let stage3 <- mkBypassWire;

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage_2;
        // We're going to assume the cache contents are an instruction. If we're
        // wrong, the result will be ignored anyway. This should reduce logic.
        InstFields fields = unpack(s.cache);
        Word imm_i = signExtend({fields.funct7, fields.rs2});

        let {x1, x2} = regfile.read_result;

        // Observation: the three cases for this are as follows:
        //    'b1100011: return x2; // Bxx
        //    'b0110011: return x2; // ALU reg
        //    'b0010011: return imm_i; // ALU imm
        // I had originally expressed this as those three followed by a
        // `default: ?` case, expecting that the undefined value would make it
        // through to Verilog and get optimized by Yosys. Bluespec, however,
        // makes a decision on what the undefined value should be, generating
        // more logic.
        //
        // Note that if you k-map that table, it's bit 5 that actually makes the
        // decision in the defined cases. So:
        let comp_rhs = case (fields.opcode[5]) matches
            'b1: return x2; // Bxx, ALU reg
            'b0: return imm_i; // ALU imm
        endcase;

        // Get the comparison started one cycle early.
        let diff_lo = {1'b0, x1[23:0]} + {1'b1, ~comp_rhs[23:0]} + 1;

        stage3 <= Stage3
            { cs: s.cs
            , cache: s.cache
            , x1: x1
            , x2: x2
            , diff_lo: diff_lo
            , rhs: comp_rhs
            };
    endrule

    interface Put feed = toPut(asReg(s));
    interface Get out = wireGet(stage3);
    method state = s;
endmodule

///////////////////////////////////////////////////////////////////////////////
// Stage 3 module

module mkStage3#(
    TwistyBus#(aw) bus,
    Stage3#(aw) start_state
) (Pipe#(Stage3#(aw), Stage4#(aw)))
provisos (Add#(xlen_m2, 2, XLEN), Add#(aw, dropped_msbs, xlen_m2));
    let s <- mkReg(start_state);
    let stage4 <- mkBypassWire;

    let no_write = replicate(tagged Invalid);

    let barrel_shifter <- mkUniqueWrapper(barrel_shift_datapath);

    // Crops a Word value for use as a smaller word address of addr_width bits.
    function Bit#(aw) crop_addr(Word addr);
        Bit#(xlen_m2) div4 = truncateLSB(addr);
        return truncate(div4);
    endfunction

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage3_reset (s.cs.state matches tagged ResetState);
        stage4 <= Stage4
            { cs: CoreState
                { hart: s.cs.hart
                , pc: s.cs.pc
                , state: tagged RunState
                }
            , rf_write: tagged Invalid
            };
        bus.issue(s.cs.pc, no_write);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage3_run (s.cs.state matches tagged RunState);
        let inst = s.cache;

        let diff_hi = {1'b0, s.x1[31:24]}
            + {1'b1, ~s.rhs[31:24]}
            + {0, s.diff_lo[24]};
        let difference = {diff_hi, s.diff_lo[23:0]};
        let signed_less_than = unpack(
            (s.x1[31] ^ s.rhs[31]) != 0 ? s.x1[31] : difference[32]);
        let unsigned_less_than = unpack(difference[32]);

        InstFields fields = unpack(inst);

        Word imm_i = signExtend(inst[31:20]);
        Word imm_s = signExtend({inst[31:25], inst[11:7]});
        Word imm_u = {inst[31:12], 0};
        Word imm_j = {
            signExtend(inst[31]), inst[19:12], inst[20], inst[30:21], 1'b0};
        Word imm_b = {
            signExtend(inst[31]), inst[7], inst[30:25], inst[11:8], 1'b0};

        let pc00 = {s.cs.pc, 2'b00};

        Word pc1 = {extend(s.cs.pc) + 1, 2'b00};
        Bit#(aw) next_pc = crop_addr(pc1); // we will MUTATE this for jumps!

        // Behold, the Big Fricking RV32I Case Discriminator!
        let next_state = tagged RunState;
        Vector#(4, Maybe#(Bit#(8))) mem_write_data = replicate(tagged Invalid);
        let other_addr = tagged Invalid;
        Maybe#(Tuple2#(RegId, Word)) rf_write = tagged Invalid;
        case (fields.opcode) matches
            // LUI
            'b0110111: rf_write = tagged Valid tuple2(fields.rd, imm_u);
            // AUIPC
            'b0010111: rf_write = tagged Valid tuple2(fields.rd, extend(pc00) + imm_u);
            // JAL
            'b1101111: begin
                next_pc = truncateLSB(pc00 + truncate(imm_j));
                rf_write = tagged Valid tuple2(fields.rd, pc1);
            end
            // JALR
            'b1100111: begin
                rf_write = tagged Valid tuple2(fields.rd, pc1);
                next_pc = crop_addr(s.x1 + imm_i);
            end
            // Bxx
            'b1100011: begin
                let condition = case (fields.funct3) matches
                    'b000: return s.x1 == s.x2;
                    'b001: return s.x1 != s.x2;
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
                let ea = s.x1 + imm_i;
                let aligned = case (fields.funct3) matches
                    'b010: (ea[1:0] == 0);
                    'b?01: (ea[0] == 0);
                    'b?00: True;
                    default: False;
                endcase;

                other_addr = tagged Valid crop_addr(ea);
                if (aligned) next_state = tagged LoadState {
                    rd: fields.rd,
                    lsbs: ea[1:0],
                    saved_funct3: fields.funct3
                };
                else next_state = tagged HaltState;
            end
            // Sx
            'b0100011: begin
                let ea = s.x1 + imm_s;
                let lsbs = ea[1:0];
                let aligned = case (fields.funct3) matches
                    'b000: True;
                    'b001: (ea[1] == 0);
                    'b010: (ea[1:0] == 0);
                    default: False;
                endcase;
                other_addr = tagged Valid crop_addr(ea);
                if (aligned) begin
                    next_state = tagged ResetState;
                    function Maybe#(Bit#(8)) bytelane(Integer i);
                        Bit#(2) ibits = fromInteger(i);
                        return case (fields.funct3[1:0]) matches
                            'b00: (ea[1:0] == ibits
                                ? tagged Valid (s.x2[7:0])
                                : tagged Invalid);
                            'b01: (ea[1] == ibits[1]
                                ? tagged Valid (ibits[0] == 1
                                    ? s.x2[15:8] : s.x2[7:0])
                                : tagged Invalid);
                            'b10: tagged Valid ((s.x2 >> {ibits, 3'b000})[7:0]);
                        endcase;
                    endfunction
                    mem_write_data = genWith(bytelane);
                end else next_state = tagged HaltState;
            end
            // ALU reg/immediate
            'b0?10011: begin
                let is_reg = fields.opcode[5];

                let alu_result = ?;
                case (fields.funct3) matches
                    'b000: begin // ADDI / ADD / SUB
                        let sub = is_reg & fields.funct7[5];
                        alu_result = sub != 0
                            ? truncate(difference)
                            : s.x1 + s.rhs;
                    end
                    // Left shift
                    'b001: begin
                        let x <- barrel_shifter.func(tuple4(
                            s.x1, s.rhs[4:0], Left, ?));
                        alu_result = x;
                    end
                    // SLTI / SLT
                    'b010: alu_result = signed_less_than ? 1 : 0;
                    // SLTIU / SLTU
                    'b011: alu_result = unsigned_less_than ? 1 : 0;
                    'b100: alu_result = s.x1 ^ s.rhs; // XORI / XOR
                    'b101: begin
                        let x <- barrel_shifter.func(tuple4(
                            s.x1, s.rhs[4:0], Right, fields.funct7[5] == 1));
                        alu_result = x;
                    end
                    'b110: alu_result = s.x1 | s.rhs; // ORI / OR
                    'b111: alu_result = s.x1 & s.rhs; // ANDI / AND
                endcase
                rf_write = tagged Valid tuple2(fields.rd, alu_result);
            end
            default: next_state = tagged HaltState;
        endcase

        let a = fromMaybe(next_pc, other_addr);
        stage4 <= Stage4
            { cs: CoreState
                { hart: s.cs.hart
                , pc: next_pc
                , state: next_state
                }
            , rf_write: rf_write
            };
        bus.issue(a, mem_write_data);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage3_load (s.cs.state matches tagged LoadState .f);
        let size = f.saved_funct3[1:0];
        let zext = f.saved_funct3[2] == 1;

        let shifted <- barrel_shifter.func(tuple4(
            s.cache, {f.lsbs, 3'b0}, Right, ?));

        let val = case (size) matches
            'b00: begin
                let b = shifted[7:0];
                return zext ? extend(b) : signExtend(b);
            end
            'b01: begin
                let b = shifted[15:0];
                return zext ? extend(b) : signExtend(b);
            end
            default: s.cache;
        endcase;
        stage4 <= Stage4
            { cs: CoreState
                { hart: s.cs.hart
                , pc: s.cs.pc
                , state: tagged RunState
                }
            , rf_write: tagged Valid tuple2(f.rd, val)
            };
        bus.issue(s.cs.pc, no_write);
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage3_halt (s.cs.state matches tagged HaltState);
        stage4 <= Stage4 { cs: s.cs, rf_write: tagged Invalid };
        bus.issue(s.cs.pc, no_write);
    endrule

    interface Put feed = toPut(asReg(s));
    interface Get out = wireGet(stage4);
    method state = s;
endmodule

///////////////////////////////////////////////////////////////////////////////
// Stage 4 module

module mkStage4#(
    RegFile2H regfile,
    TwistyBus#(aw) bus,
    Stage4#(aw) start_state
) (Pipe#(Stage4#(aw), Stage1#(aw)));
    let s <- mkReg(start_state);
    let stage1 <- mkBypassWire;

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage_4;
        let response = bus.response;
        if (s.rf_write matches tagged Valid {.rd, .value})
            regfile.write(s.cs.hart, rd, value);

        stage1 <= Stage1
            { cs: s.cs
            , cache: response
            };
    endrule

    interface Put feed = toPut(asReg(s));
    interface Get out = wireGet(stage1);
    method state = s;
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

function Get#(a) wireGet(Wire#(a) w);
    return interface Get;
        method ActionValue#(a) get;
            return w;
        endmethod
    endinterface;
endfunction

function Word barrel_shift_datapath(Tuple4#(Word, Bit#(5), ShiftDir, Bool) args);
    let {lhs, amt, dir, sext} = args;
    let prepared_lhs = case (dir) matches
        Left: reverseBits(lhs);
        Right: lhs;
    endcase;
    bit fill = msb(lhs) & pack(sext);
    Int#(33) ext = unpack({fill, lhs});
    let shifted = truncate(pack(ext >> amt));
    return case (dir) matches
        Left: reverseBits(shifted);
        Right: shifted;
    endcase;
endfunction

endpackage

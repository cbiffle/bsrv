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
// instructions take twice as long due to bus contention, and shift
// instructions take a rather long time to save space.)

package Twisty5;

import BRAMCore::*;
import Vector::*;

import Common::*;

typedef 4 HartCount;
typedef Bit#(TLog#(HartCount)) HartId;

interface TwistyBus#(numeric type addr_width);
    (* always_ready *)
    method Action issue(
        Bit#(addr_width) address,
        Vector#(4, Maybe#(Bit#(8))) write_data);
    (* always_ready *)
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

typedef enum {
    SerialShifter,
    LeapShifter,
    BarrelShifter
} ShifterFlavor deriving (Eq, FShow);

typedef enum { Left, Right } ShiftDir deriving (Bits, FShow);

typedef union tagged {
    BaseHartState Base;
    struct {
        bit fill;
        ShiftDir dir;
        UInt#(5) amt;
    } ShiftState;
} HartState deriving (Bits, FShow);

typedef union tagged {
    void ResetState;
    void RunState;
    RegId LoadState;
    void HaltState;
} BaseHartState deriving (Bits, FShow);

typedef struct {
    HartId hart;
    Bit#(addr_width) pc;
    HartState state;
} CoreState#(numeric type addr_width) deriving (Bits, FShow);

typedef struct {
    CoreState#(addr_width) cs;
    Word cache;
} Stage1#(numeric type addr_width) deriving (Bits, FShow);

instance DefaultValue#(Stage1#(addr_width));
    defaultValue = Stage1
        { cs: CoreState
            { hart: 2
            , pc: 2 * 2
            , state: tagged Base tagged ResetState
            }
        , cache: 0
        };
endinstance

typedef struct {
    CoreState#(addr_width) cs;
    Word cache;
} Stage2#(numeric type addr_width) deriving (Bits, FShow);

instance DefaultValue#(Stage2#(addr_width));
    defaultValue = Stage2
        { cs: CoreState
            { hart: 1
            , pc: 1 * 2
            , state: tagged Base tagged ResetState
            }
        , cache: 0
        };
endinstance

typedef struct {
    CoreState#(addr_width) cs;
    Word cache;
    Word x1;
    Word x2;
    Bit#(25) diff_lo;
    Word rhs;
} Stage3#(numeric type addr_width) deriving (Bits, FShow);

instance DefaultValue#(Stage3#(addr_width));
    defaultValue = Stage3
        { cs: CoreState
            { hart: 0
            , pc: 0 * 2
            , state: tagged Base tagged ResetState
            }
        , cache: 0
        , x1: 0
        , x2: 0
        , diff_lo: 0
        , rhs: 0
        };
endinstance

typedef struct {
    CoreState#(addr_width) cs;
    Maybe#(Tuple2#(RegId, Word)) rf_write;
} Stage4#(numeric type addr_width) deriving (Bits, FShow);

instance DefaultValue#(Stage4#(addr_width));
    defaultValue = Stage4
        { cs: CoreState
            { hart: 3
            , pc: 3 * 2
            , state: tagged Base tagged ResetState
            }
        , rf_write: tagged Invalid
        };
endinstance

module mkTwisty5#(
    ShifterFlavor shifter_flavor,
    TwistyBus#(addr_width) bus
) (Twisty5#(addr_width))
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

    // The big shared regfile.
    RegFile2H regfile <- mkRegFile2H;

    ///////////////////////////////////////////////////////////////////////////
    // Stage 1 - decoding some state, starting the regfile read.

    // Input register for stage 1.
    Reg#(Stage1#(addr_width)) stage1 <- mkReg(defaultValue);
    // Input register for stage 2.
    Reg#(Stage2#(addr_width)) stage2 <- mkReg(defaultValue);

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage_1;
        let s = stage1;
        InstFields fields = unpack(s.cache);
        regfile.read(s.cs.hart, fields.rs1, fields.rs2);
        stage2 <= Stage2
            { cs: s.cs
            , cache: s.cache
            };
    endrule

    ///////////////////////////////////////////////////////////////////////////
    // Stage 2 - first part of execute.

    Reg#(Stage3#(addr_width)) stage3 <- mkReg(defaultValue);

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage_2;
        let s = stage2;

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

    ///////////////////////////////////////////////////////////////////////////
    // Stage 3

    Reg#(Stage4#(addr_width)) stage4 <- mkReg(defaultValue);

    // The main execution path, factored out of the rule below to decrease
    // indentation creep.
    function run_body(s);
        actionvalue
            let inst = (Stage3#(addr_width)'(s)).cache;

            let diff_hi = {1'b0, s.x1[31:24]}
                + {1'b1, ~s.rhs[31:24]}
                + {0, s.diff_lo[24]};
            let difference = {diff_hi, s.diff_lo[23:0]};
            let signed_less_than = unpack(
                (s.x1[31] ^ s.rhs[31]) != 0 ? s.x1[31] : difference[32]);
            let unsigned_less_than = unpack(difference[32]);

            InstFields fields = unpack(inst);

            // This is the barrel shifter, in the cheapest formulation I've
            // found for this FPGA technology. If parameters select a serial
            // shifter, the output will go unused, and we are trusting in the
            // synthesis toolchain to optimize this away.
            // Actual cases in funct3 we're distinguishing:
            //    'b001: return reverseBits(x1);
            //    'b100: return x1;
            // Manual k-mapping shows we can depend on either bit 0 or 3.
            let shifter_lhs = case (fields.funct3[0]) matches
                'b1: return reverseBits(s.x1);
                'b0: return s.x1;
            endcase;
            bit shift_fill = msb(shifter_lhs) & fields.funct7[5];
            Int#(33) shift_ext = unpack({shift_fill, shifter_lhs});
            let shifter_out = truncate(pack(shift_ext >> s.rhs[4:0]));

            Word imm_i = signExtend(inst[31:20]);
            Word imm_s = signExtend({inst[31:25], inst[11:7]});
            Word imm_u = {inst[31:12], 0};
            Word imm_j = {
                signExtend(inst[31]), inst[19:12], inst[20], inst[30:21], 1'b0};
            Word imm_b = {
                signExtend(inst[31]), inst[7], inst[30:25], inst[11:8], 1'b0};

            Bit#(addr_width) next_pc = s.cs.pc + 1; // we will MUTATE this for jumps!

            let pc00 = {s.cs.pc, 2'b00};

            // Behold, the Big Fricking RV32I Case Discriminator!
            let next_state = tagged Base tagged RunState;
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
                    rf_write = tagged Valid tuple2(fields.rd, {0, s.cs.pc + 1, 2'b00});
                end
                // JALR
                'b1100111: begin
                    rf_write = tagged Valid tuple2(fields.rd, extend({s.cs.pc + 1, 2'b00}));
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
                        default: False;
                    endcase;

                    other_addr = tagged Valid crop_addr(ea);
                    if (aligned) next_state = tagged Base tagged LoadState fields.rd;
                    else next_state = tagged Base tagged HaltState;
                end
                // Sx
                'b0100011: begin
                    let ea = s.x1 + imm_s;
                    let aligned = case (fields.funct3) matches
                        'b010: (ea[1:0] == 0);
                        default: False;
                    endcase;
                    other_addr = tagged Valid crop_addr(ea);
                    if (aligned) begin
                        next_state = tagged Base tagged ResetState;
                        function Maybe#(Bit#(8)) bytelane(Integer i);
                            return tagged Valid ((s.x2 >> (8 * i))[7:0]);
                        endfunction
                        mem_write_data = genWith(bytelane);
                    end else next_state = tagged Base tagged HaltState;
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
                        'b001: case (shifter_flavor) matches
                            BarrelShifter: alu_result = reverseBits(shifter_out);
                            default: begin
                                let shift_dist = s.rhs[4:0];
                                next_state = tagged ShiftState {
                                    amt: unpack(shift_dist),
                                    fill: 0,
                                    dir: Left
                                };
                                alu_result = s.x1;
                            end
                        endcase
                        // SLTI / SLT
                        'b010: alu_result = signed_less_than ? 1 : 0;
                        // SLTIU / SLTU
                        'b011: alu_result = unsigned_less_than ? 1 : 0;
                        'b100: alu_result = s.x1 ^ s.rhs; // XORI / XOR
                        'b101: case (shifter_flavor) matches
                            BarrelShifter: alu_result = shifter_out;
                            default: begin
                                let shift_dist = s.rhs[4:0];
                                let fill = fields.funct7[5] & s.x1[31];
                                next_state = tagged ShiftState {
                                    amt: unpack(shift_dist),
                                    fill: fill,
                                    dir: Right
                                };
                                alu_result = s.x1;
                            end
                        endcase
                        'b110: alu_result = s.x1 | s.rhs; // ORI / OR
                        'b111: alu_result = s.x1 & s.rhs; // ANDI / AND
                    endcase
                    rf_write = tagged Valid tuple2(fields.rd, alu_result);
                end
                default: next_state = tagged Base tagged HaltState;
            endcase

            let a = fromMaybe(next_pc, other_addr);
            let s4 = Stage4
                { cs: CoreState
                    { hart: s.cs.hart
                    , pc: next_pc
                    , state: next_state
                    }
                , rf_write: rf_write
                };
            let ba = tuple2(a, mem_write_data);
            return tuple2(s4, ba);
        endactionvalue
    endfunction

    (* fire_when_enabled *)
    rule do_stage_3;
        let s = stage3;
        $display(fshow(s));
        let no_write = replicate(tagged Invalid);

        let t <- case (s.cs.state) matches
            tagged Base (tagged ResetState): return (actionvalue
                let s4 = Stage4
                    { cs: CoreState
                        { hart: s.cs.hart
                        , pc: s.cs.pc
                        , state: tagged Base tagged RunState
                        }
                    , rf_write: tagged Invalid
                    };
                return tuple2(s4, tuple2(s.cs.pc, no_write));
            endactionvalue);
            tagged Base (tagged LoadState .rd): return (actionvalue
                let s4 = Stage4
                    { cs: CoreState
                        { hart: s.cs.hart
                        , pc: s.cs.pc
                        , state: tagged Base tagged RunState
                        }
                    , rf_write: tagged Valid tuple2(rd, s.cache)
                    };
                return tuple2(s4, tuple2(s.cs.pc, no_write));
            endactionvalue);
            tagged ShiftState .flds &&& (shifter_flavor != BarrelShifter): return (actionvalue
                let by_byte = shifter_flavor == LeapShifter && flds.amt > 8;
                let r = by_byte ? begin
                    case (flds.dir) matches
                        Left: {truncate(s.x1), 8'b0};
                        Right: {Bit#(8)'(signExtend(flds.fill)), truncateLSB(s.x1)};
                    endcase
                end : begin
                    case (flds.dir) matches
                        Left: {truncate(s.x1), 1'b0};
                        Right: {flds.fill, truncateLSB(s.x1)};
                    endcase
                end;
                InstFields fields = unpack(s.cache);
                let rf_write = (flds.amt != 0)
                    ? tagged Valid tuple2(fields.rd, r)
                    : tagged Invalid;

                let next = (flds.amt == 0)
                    ? tagged Base tagged RunState
                    : tagged ShiftState {
                        amt: flds.amt - (by_byte ? 8 : 1),
                        dir: flds.dir,
                        fill: flds.fill
                    };

                let s4 = Stage4
                    { cs: CoreState
                        { hart: s.cs.hart
                        , pc: s.cs.pc
                        , state: next
                        }
                    , rf_write: rf_write
                    };

                // We'll issue a dummy fetch for the next instruction during
                // every cycle of the shift, to maintain transaction ordering.
                return tuple2(s4, tuple2(s.cs.pc, no_write));
            endactionvalue);
            tagged Base (tagged RunState): return run_body(s);
            default: return (actionvalue
                let s4 = Stage4 { cs: s.cs, rf_write: tagged Invalid };
                return tuple2(s4, tuple2(s.cs.pc, no_write));
            endactionvalue);
        endcase;

        let {s4, busreq} = t;
        let {addr, data} = busreq;
        bus.issue(addr, data);
        stage4 <= s4;
    endrule

    ///////////////////////////////////////////////////////////////////////////
    // Stage 4 - bus response

    let stage1_wire <- mkBypassWire;

    (* fire_when_enabled, no_implicit_conditions *)
    rule do_stage_4;
        let response = bus.response;
        let s = stage4;

        if (s.rf_write matches tagged Valid {.rd, .value})
            regfile.write(s.cs.hart, rd, value);

        stage1_wire <= Stage1
            { cs: s.cs
            , cache: response
            };
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule close_the_loop;
        stage1 <= stage1_wire;
    endrule

    method HartId next_hart_id = stage3.cs.hart;
    method HartState next_hart_state = stage3.cs.state;
    method Bool halted = stage3.cs.state matches tagged Base(tagged HaltState) ? True : False;
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

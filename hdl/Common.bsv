// Shared parts useful for RISC-V implementations.

package Common;

import BRAMCore::*;

// Number of bits in an x register (general purpose register).
typedef 32 XLEN;
// Type held in general purpose registers.
typedef Bit#(XLEN) Word;
// Number of general purpose registers defined.
typedef 32 RegCount;
// Type used to address general purpose registers.
typedef Bit#(TLog#(RegCount)) RegId;

// Fields of a 32-bit instruction. Not every instruction uses _all_ these
// fields, and the fields are often concatenated to form immediates, etc.
//
// The ordering of these fields is chosen so that an instruction word can be
// decoded by using 'unpack'.
typedef struct {
    Bit#(7) funct7;
    RegId rs2;
    RegId rs1;
    Bit#(3) funct3;
    RegId rd;
    Bit#(7) opcode;
} InstFields deriving (Bits, FShow);

// Rough equivalent of Verilog 'signed' function. Useful for forcing sign
// extension in shifts.
function Int#(XLEN) toSigned(Word x);
    return unpack(x);
endfunction

// Typeclass implemented by enumeration 'e' to declare that it identifies bits
// in a onehot encoding of 'n' bits.
//
// To implement this, you must ensure that the largest value of 'e' is less than
// 'n'.
typeclass OneHotIndex#(type e, numeric type n)
    provisos (Bounded#(e))
    dependencies (e determines n);
endtypeclass

// Utility for converting an enum variant to a onehot encoding.
function Bit#(n) onehot_state(e state)
provisos (OneHotIndex#(e, n), Bits#(e, x));
    return 1 << pack(state);
endfunction

// Utility for checking a onehot encoding for the presence of a bit encoded by
// an enum variant.
//
// Note that using this in the guard condition for a rule will usually require
// an explicit 'mutually_exclusive' pragma.
function Bool is_onehot_state(Bit#(n) bits, e state)
provisos (OneHotIndex#(e, n), Bits#(e, x));
    return bits[pack(state)] != 0;
endfunction

// An initiator on the DinkyBus (typically a CPU).
//
// DinkyBus is parameterized in terms of address width. Note that addresses are
// in terms of 32-bit words, so the maximum practical 'addr_width' given 'XLEN'
// is 30. Smaller values generate less logic.
//
// This bus does not use a read strobe for simplicity (read is implied by
// not-write), which may cause problems for read-sensitive I/O devices. I plan
// to burn that bridge when I come to it.
interface DinkyBusInit#(numeric type addr_width);
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
endinterface

///////////////////////////////////////////////////////////////////////////////
// Pseudo-dual-port register file compatible with iCE40 BRAM.
//
// iCE40 BRAM has one dedicated read port and one dedicated write port, while
// Bluespec expects two read/write ports. By only using read on one port and
// write on the other, we can get an equivalent result.
//
// Note that synthesizing this with Yosys requires replacing Bluespec's
// supplied BRAM Verilog with our simplified copy.

interface RegFile1;
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
module mkRegFile1 (RegFile1);
    BRAM_DUAL_PORT#(RegId, Word) regfile <- mkBRAMCore2(valueof(RegCount), False);

    method Action read(RegId index);
        regfile.a.put(False, index, ?);
    endmethod

    method Action write(RegId index, Word value);
        if (index != 0) regfile.b.put(True, index, value);
    endmethod

    method Word read_result = regfile.a.read;
endmodule

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

interface RegFile2;
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
module mkRegFile2 (RegFile2);
    BRAM_DUAL_PORT#(RegId, Word) rf0 <- mkBRAMCore2(valueof(RegCount), False);
    BRAM_DUAL_PORT#(RegId, Word) rf1 <- mkBRAMCore2(valueof(RegCount), False);

    method Action read(RegId rs1, RegId rs2);
        rf0.a.put(False, rs1, ?);
        rf1.a.put(False, rs2, ?);
    endmethod

    method Action write(RegId index, Word value);
        if (index != 0) begin
            rf0.b.put(True, index, value);
            rf1.b.put(True, index, value);
        end
    endmethod

    method Tuple2#(Word, Word) read_result = tuple2(rf0.a.read, rf1.a.read);
endmodule

endpackage

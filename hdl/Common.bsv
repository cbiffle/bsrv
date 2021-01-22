// Shared parts useful for RISC-V implementations.

package Common;

// Number of bits in an x register (general purpose register).
typedef 32 XLEN;
// Type held in general purpose registers.
typedef Bit#(XLEN) Word;
// Number of general purpose registers defined.
typedef 32 RegCount;
// Type used to address general purpose registers.
typedef Bit#(TLog#(RegCount)) RegId;

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

endpackage

// A trivial SoC around the Twisty5 core, providing just enough meat to provide
// a realistic synthesis result.
//
// This consists of the CPU and some RAM containing a fixed program, with the
// bottom bits of the address bus available for probing.
package Twisty5Soc;

import BRAMCore::*;
import FIFO::*;
import Vector::*;

import Common::*;
import Twisty5::*;

interface Twisty5Soc;
    method Bit#(5) led;
endinterface

(* synthesize *)
module mkTwisty5Soc (Twisty5Soc);
    BRAM_PORT#(Bit#(8), Word) ram <- mkBRAMCore1Load(256, False, "../hdl/examples/demoprog.readmemb", True);

    let issue_wire <- mkWire;

    Twisty5#(8) core <- mkTwisty5(interface TwistyBus#(8);
        method Action issue(Bit#(8) address, Bool write, Word data);
            issue_wire <= tuple3(write, address, data);
        endmethod
        method Word response;
            return ram.read;
        endmethod
    endinterface);

    (* fire_when_enabled *)
    rule drive_ram;
        let {w, a, d} = issue_wire;
        ram.put(w, a, d);
    endrule

    method Bit#(5) led = truncate(pack(core.next_hart_state));
endmodule

endpackage

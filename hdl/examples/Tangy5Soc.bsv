// A trivial SoC around the Tangy5 core, providing just enough meat to provide
// a realistic synthesis result.
//
// This consists of the CPU and some RAM containing a fixed program, with the
// bottom bits of the address bus available for probing.
package Tangy5Soc;

import BRAMCore::*;
import Vector::*;

import Common::*;
import Tangy5::*;

interface Tangy5Soc;
    method Bit#(5) led;
endinterface

(* synthesize *)
module mkTangy5Soc (Tangy5Soc);
    BRAM_PORT#(Bit#(8), Word) ram <- mkBRAMCore1(256, False);

    Tangy5#(8) core <- mkTangy5(interface DinkyBus;
        method issue(a, w, d) = ram.put(w, a, d);
        method response = ram.read;
    endinterface);

    method Bit#(5) led = extend(core.core_state);
endmodule

endpackage

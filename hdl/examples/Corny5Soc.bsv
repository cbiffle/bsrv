// A trivial SoC around the Corny5 core, providing just enough meat to provide
// a realistic synthesis result.
//
// This consists of the CPU and some RAM containing a fixed program, with the
// bottom bits of the address bus available for probing.
package Corny5Soc;

import BRAMCore::*;
import Vector::*;

import Common::*;
import Rvfi::*;
import Corny5::*;

interface Corny5Soc;
    method Bit#(5) led;
endinterface

(* synthesize *)
module mkCorny5Soc (Corny5Soc);
    BRAM_PORT_BE#(Bit#(8), Word, 4) ram <- mkBRAMCore1BELoad(256, False, "../hdl/examples/demoprog.readmemb", True);

    Corny5#(8) core <- mkCorny5(interface DinkyBus;
        method issue(a, w, d) = ram.put(w, a, d);
        method response = ram.read;
    endinterface, noRvfi);

    method Bit#(5) led = extend(pack(core.core_state));
endmodule

endpackage

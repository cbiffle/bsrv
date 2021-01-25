// A trivial SoC around the Dinky5 core, providing just enough meat to provide
// a realistic synthesis result.
//
// This consists of the CPU and some RAM containing a fixed program, with the
// bottom bits of the address bus available for probing.
package Dinky5Soc;

import BRAMCore::*;
import Vector::*;

import Common::*;
import Dinky5::*;

interface Dinky5Soc;
    method Bit#(5) led;
endinterface

(* synthesize *)
module mkDinky5Soc (Dinky5Soc);
    BRAM_PORT#(Bit#(8), Word) ram <- mkBRAMCore1Load(256, False, "../hdl/examples/demoprog.readmemb", True);

    Dinky5#(8) core <- mkDinky5(interface DinkyBus;
        method issue(address, write, data) = ram.put(write, address, data);
        method response = ram.read;
    endinterface);

    method Bit#(5) led = truncate(core.core_state);
endmodule

endpackage

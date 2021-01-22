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
    Dinky5#(8) core <- mkDinky5;

    BRAM_PORT#(Bit#(8), Word) ram <- mkBRAMCore1Load(256, False, "../hdl/examples/demoprog.readmemb", True);

    rule memory_drive;
        ram.put(core.bus.mem_write, core.bus.mem_addr, core.bus.mem_data);
    endrule

    rule memory_result;
        core.bus.mem_result(ram.read);
    endrule

    method Bit#(5) led = truncate(core.core_state);
endmodule

endpackage

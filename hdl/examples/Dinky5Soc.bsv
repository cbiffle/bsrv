// A trivial SoC around the Dinky5 core, providing just enough meat to provide
// a realistic synthesis result.
//
// This consists of the CPU and some RAM containing a fixed program, with the
// bottom bits of the address bus available for probing.
package Dinky5Soc;

import BRAMCore::*;
import Vector::*;

import Dinky5::*;

interface Dinky5Soc;
    method Bit#(5) led;
endinterface

(* synthesize *)
module mkDinky5Soc (Dinky5Soc);
    Dinky5#(7) core <- mkDinky5;

    BRAM_PORT#(Bit#(7), Word) ram <- mkBRAMCore1(128, False);

    rule memory_drive;
        ram.put(core.mem_write, core.mem_addr, core.mem_data);
    endrule

    rule memory_result;
        core.mem_result(ram.read);
    endrule

    method Bit#(5) led = truncate(core.mem_addr);
endmodule

endpackage

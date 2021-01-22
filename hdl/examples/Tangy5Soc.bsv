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
    Tangy5#(8) core <- mkTangy5;

    BRAM_PORT#(Bit#(8), Word) ram <- mkBRAMCore1(256, False);

    rule memory_drive;
        ram.put(core.bus.mem_write, core.bus.mem_addr, core.bus.mem_data);
    endrule

    rule memory_result;
        core.bus.mem_result(ram.read);
    endrule

    method Bit#(5) led = truncate(core.bus.mem_addr);
endmodule

endpackage

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
    method Bit#(32) out;
    method HartId next_hart_id;
    method HartState next_hart_state;
endinterface

(* synthesize *)
module mkTwisty5Soc (Twisty5Soc);
    BRAM_PORT#(Bit#(8), Word) ram <- mkBRAMCore1Load(256, False,
        "../hdl/examples/twisty.readmemb", True);

    let issue_wire <- mkWire;
    let outport <- mkReg(0);

    Twisty5#(9) core <- mkTwisty5(interface TwistyBus#(9);
        method Action issue(Bit#(9) address, Bool write, Word data);
            let {io, addr} = split(address);
            if (io == 1'b1) begin
                if (write) outport <= data;
            end else issue_wire <= tuple3(write, addr, data);
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

    method Bit#(32) out = outport;
    method HartId next_hart_id = core.next_hart_id;
    method HartState next_hart_state = core.next_hart_state;
endmodule

endpackage

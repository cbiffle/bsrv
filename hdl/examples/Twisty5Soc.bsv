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
module mkTwisty5Soc#(ShifterFlavor shifter_flavor) (Twisty5Soc);
    BRAM_PORT_BE#(Bit#(8), Word, 4) ram <- mkBRAMCore1BELoad(256, False,
        "../hdl/examples/twisty.readmemb", True);

    let issue_wire <- mkWire;
    let outport <- mkReg(0);
    let outport1 <- mkReg(0);
    let outport2 <- mkReg(0);

    function Action lanewrite(Reg#(Word) r, Vector#(4, Maybe#(Bit#(8))) data);
        return action
            r <= {
                fromMaybe(r[31:24], data[3]),
                fromMaybe(r[23:16], data[2]),
                fromMaybe(r[15:8], data[1]),
                fromMaybe(r[7:0], data[0])
            };
        endaction;
    endfunction

    Twisty5#(9) core <- mkTwisty5(shifter_flavor, interface TwistyBus#(9);
        method Action issue(address, write_data);
            let {io, addr} = split(address);
            if (io == 1'b1) lanewrite(outport, write_data);
            else issue_wire <= tuple2(addr, write_data);
        endmethod
        method Word response;
            return ram.read;
        endmethod
    endinterface);

    (* fire_when_enabled *)
    rule drive_ram;
        let {a, wd} = issue_wire;
        ram.put(pack(map(isValid, wd)), a, pack(map(fromMaybe(?), wd)));
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule clock_outport;
        outport1 <= outport;
        outport2 <= outport1;
    endrule

    method Bit#(32) out = outport2;
    method HartId next_hart_id = core.next_hart_id;
    method HartState next_hart_state = core.next_hart_state;
endmodule

endpackage

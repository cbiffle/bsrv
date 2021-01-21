package Examples;

import Board::*;

import Dinky5Soc::*;

(* synthesize, default_clock_osc="clk_12mhz" *)
module mkDinky (Top);
    Dinky5Soc soc <- mkDinky5Soc;

    method led = soc.led;

    interface FTDI ftdi;
        method Bit#(1) rxd = 1;
        method Action txd(Bit#(1) val) = noAction;
    endinterface
endmodule

endpackage : Examples

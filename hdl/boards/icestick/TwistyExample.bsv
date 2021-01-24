package TwistyExample;

import Board::*;

import Twisty5Soc::*;

(* synthesize, default_clock_osc="clk_12mhz" *)
module mkTwisty (Top);
    Twisty5Soc soc <- mkTwisty5Soc;

    method led = soc.led;

    interface FTDI ftdi;
        method Bit#(1) rxd = 1;
        method Action txd(Bit#(1) val) = noAction;
    endinterface
endmodule

endpackage

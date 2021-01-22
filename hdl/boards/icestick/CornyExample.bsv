package CornyExample;

import Board::*;

import Corny5Soc::*;

(* synthesize, default_clock_osc="clk_12mhz" *)
module mkCorny (Top);
    Corny5Soc soc <- mkCorny5Soc;

    method led = soc.led;

    interface FTDI ftdi;
        method Bit#(1) rxd = 1;
        method Action txd(Bit#(1) val) = noAction;
    endinterface
endmodule

endpackage

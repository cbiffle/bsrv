package TangyExample;

import Board::*;

import Tangy5Soc::*;

(* synthesize, default_clock_osc="clk_12mhz" *)
module mkTangy (Top);
    Tangy5Soc soc <- mkTangy5Soc;

    method led = soc.led;
    method logic_port = 0;
    method dcd_n = 0;

    interface FTDI ftdi;
        method Bit#(1) rxd = 1;
        method Action txd(Bit#(1) val) = noAction;
    endinterface
endmodule

endpackage

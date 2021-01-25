package TwistyExample;

import Clocks::*;

import Board::*;
import Twisty5Soc::*;

(* synthesize, default_clock_osc="clk_12mhz" *)
module mkTwisty (Top);
    let clk_12mhz <- exposeCurrentClock;
    let dtr_reset <- exposeCurrentReset;
    let reset_invert <- mkResetInverter(dtr_reset);

    let reset_gen <- mkResetSync(2, True, clk_12mhz, reset_by reset_invert);

    let innards <- mkTwistyX(reset_by reset_gen.new_rst);

    return innards;
endmodule

module mkTwistyX (Top);
    Reg#(Bit#(24)) ctr <- mkReg(12_000_000);
    rule downcount;
        if (ctr == 0) ctr <= 12_000_000;
        else ctr <= ctr - 1;
    endrule

    Twisty5Soc soc <- mkTwisty5Soc;

    method led = {truncate(soc.out), ctr[23]};
    method dcd_n = 0;
    method logic_port = {truncate(soc.out), soc.next_hart_id};

    interface FTDI ftdi;
        method Bit#(1) rxd = 1;
        method Action txd(Bit#(1) val) = noAction;
    endinterface
endmodule

endpackage

package TwistyExample;

import Clocks::*;

import Board::*;
import Twisty5::*;
import Twisty5Soc::*;

(* synthesize, default_clock_osc="clk_25mhz", default_reset="btn_pwr" *)
module mkTwisty (Top);
    let clk_25mhz <- exposeCurrentClock;
    let dtr_reset <- exposeCurrentReset;
    let reset_invert <- mkResetInverter(dtr_reset);

    let reset_gen <- mkResetSync(2, True, clk_25mhz, reset_by reset_invert);

    Reg#(Bit#(4)) pll_lock_window <- mkReg(0, reset_by reset_gen.new_rst);

    let pll_stable = &pll_lock_window;

    MakeResetIfc stable_reset <- mkResetSync(8, True, clk_25mhz,
        reset_by reset_gen.new_rst);

    rule step_pll_output_monitor;
        pll_lock_window <= {truncate(pll_lock_window), pack(True)};
        if (pll_stable == 0) stable_reset.assertReset;
    endrule

    let innards <- mkTwistyX(clocked_by clk_25mhz, reset_by stable_reset.new_rst);

    return innards;
endmodule

module mkTwistyX (Top);
    Reg#(Bit#(24)) ctr <- mkReg(12_000_000);
    rule downcount;
        if (ctr == 0) ctr <= 12_000_000;
        else ctr <= ctr - 1;
    endrule

    Twisty5Soc soc <- mkTwisty5Soc;

    let dsp <- mkDummySerialPort;

    method leds = {truncate(soc.out), ctr[23]};
    method buttons(_) = noAction;
    method dip_switches(_) = noAction;

    interface SerialPort serial = dsp;
endmodule

endpackage

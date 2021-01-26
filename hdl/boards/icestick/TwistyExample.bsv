package TwistyExample;

import Clocks::*;

import Board::*;
import Ice40Pll::*;
import Twisty5::*;
import Twisty5Soc::*;

(* synthesize, default_clock_osc="clk_12mhz" *)
module mkTwisty (Top);
    let clk_12mhz <- exposeCurrentClock;
    let dtr_reset <- exposeCurrentReset;
    let reset_invert <- mkResetInverter(dtr_reset);

    let reset_gen <- mkResetSync(2, True, clk_12mhz, reset_by reset_invert);

    Ice40PllCore pll <- mkIce40PllCore(
        "SIMPLE",
        "FIXED",
        "FIXED",
        "GENCLK",
        4'b1111,
        4'b1111,
        0,
        49,
        3,
        1,
        clk_12mhz,
        reset_by reset_gen.new_rst
    );
    let clk_hi = pll.clk_out_global;

    Reg#(Bit#(4)) pll_lock_window <- mkReg(0, reset_by reset_gen.new_rst);

    let pll_stable = &pll_lock_window;

    MakeResetIfc stable_reset <- mkResetSync(8, True, clk_hi,
        reset_by reset_gen.new_rst);

    rule step_pll_output_monitor;
        pll_lock_window <= {truncate(pll_lock_window), pack(pll.lock)};
        if (pll_stable == 0) stable_reset.assertReset;
    endrule

    let innards <- mkTwistyX(clocked_by clk_hi, reset_by stable_reset.new_rst);

    return innards;
endmodule

module mkTwistyX (Top);
    Reg#(Bit#(24)) ctr <- mkReg(12_000_000);
    rule downcount;
        if (ctr == 0) ctr <= 12_000_000;
        else ctr <= ctr - 1;
    endrule

    let shifter_flavor =
`ifdef TWISTY_BARREL_SHIFTER
        BarrelShifter;
`elsif TWISTY_LEAP_SHIFTER
        LeapShifter;
`else
        SerialShifter;
`endif

    Twisty5Soc soc <- mkTwisty5Soc(shifter_flavor);

    method led = {truncate(soc.out), ctr[23]};
    method dcd_n = 0;
    method logic_port = {truncate(soc.out), soc.next_hart_id};

    interface FTDI ftdi;
        method Bit#(1) rxd = 1;
        method Action txd(Bit#(1) val) = noAction;
    endinterface
endmodule

endpackage

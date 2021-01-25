package Ice40Pll;

interface Ice40PllCore;
  interface Clock clk_out_global;

    (* always_enabled *)
    method Action bypass;
    (* always_enabled *)
    method Bool lock;
endinterface

import "BVI" SB_PLL40_CORE =
module mkIce40PllCore #(
  String feedback_path,
  String delay_adjustment_mode_feedback,
  String delay_adjustment_mode_relative,
  String pllout_select,
  Bit#(4) fda_feedback,
  Bit#(4) fda_relative,
  Bit#(4) divr,
  Bit#(7) divf,
  Bit#(3) divq,
  Bit#(3) filter_range
) (Clock clk_in, Ice40PllCore pll);
  parameter FEEDBACK_PATH = feedback_path;
  parameter DELAY_ADJUSTMENT_MODE_FEEDBACK = delay_adjustment_mode_feedback;
  parameter DELAY_ADJUSTMENT_MODE_RELATIVE = delay_adjustment_mode_relative;
  parameter PLLOUT_SELECT = pllout_select;
  parameter FDA_FEEDBACK = fda_feedback;
  parameter FDA_RELATIVE = fda_relative;
  parameter DIVR = divr;
  parameter DIVF = divf;
  parameter DIVQ = divq;
  parameter FILTER_RANGE = filter_range;

  default_clock no_clock;
  default_reset rst(RESETB);

  method bypass() enable(BYPASS) clocked_by(clk_in);
  schedule bypass C bypass;

  method LOCK lock;
  schedule lock CF lock;

  input_clock clk_in(REFERENCECLK) = clk_in;
  output_clock clk_out_global(PLLOUTGLOBAL);
  ancestor(clk_out_global, clk_in);
endmodule

endpackage

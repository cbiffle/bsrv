// Copyright 2020 Oxide Computer Company
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

package Examples;

import Board::*;

import Blinky::*;

(* synthesize, default_clock_osc="clk_12mhz" *)
module mkBlinky (Top);
    Blinky#(12_000_000) blinky <- Blinky::mkBlinky();

    method led() = {'0, blinky.led()};

    interface FTDI ftdi;
        // Ignore FTDI IO.
        method Bit#(1) rxd() = 1;
        method Action txd(Bit#(1) val);
        endmethod
    endinterface
endmodule

endpackage : Examples

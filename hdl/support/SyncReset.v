// ---------------------------------------------------------------------------
// 
// Copyright (c) 2020 Bluespec, Inc. All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
// 
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the
//    distribution.
// 
// 3. Neither the name of the copyright holder nor the names of its
//    contributors may be used to endorse or promote products derived
//    from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// ---------------------------------------------------------------------------

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif



// A synchronization module for resets.   Output resets are held for
// RSTDELAY+1 cycles, RSTDELAY >= 0.   Both assertion and deassertions is
// synchronized to the clock.
module SyncReset (
                  IN_RST,
                  CLK,
                  OUT_RST
                  );

   parameter          RSTDELAY = 1  ; // Width of reset shift reg

   input              CLK ;
   input              IN_RST ;
   output             OUT_RST ;

   reg [RSTDELAY:0]   reset_hold ;
   wire [RSTDELAY+1:0] next_reset = {reset_hold, ~ `BSV_RESET_VALUE} ;

   assign  OUT_RST = reset_hold[RSTDELAY] ;

   always @( posedge CLK )      // reset is read synchronous with clock
     begin
       // The ternary assignment and the expansion of IN_RST ensure that the synchronizer is
       // X-pessimistic. It will immediately go to X when its input goes to X and will stay X
       // after the reset becomes defined until the Xs flush through the hold register.
       reset_hold <= `BSV_ASSIGNMENT_DELAY (IN_RST == `BSV_RESET_VALUE) ? {(RSTDELAY + 1) {IN_RST}}
                                                                        : next_reset[RSTDELAY:0];
     end // always @ ( posedge CLK )

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin
        #0 ;
        // initialize out of reset forcing the designer to do one
        reset_hold = {(RSTDELAY + 1) {~ `BSV_RESET_VALUE }} ;
     end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // SyncReset

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



module MakeReset (
		  CLK,
		  RST,
                  ASSERT_IN,
		  ASSERT_OUT,

                  DST_CLK,
                  OUT_RST
                  );

   parameter          RSTDELAY = 2  ; // Width of reset shift reg
   parameter          init = 1 ;

   input              CLK ;
   input              RST ;
   input              ASSERT_IN ;
   output             ASSERT_OUT ;

   input              DST_CLK ;
   output             OUT_RST ;

   reg                rst ;
   wire               OUT_RST ;

   assign ASSERT_OUT = rst == `BSV_RESET_VALUE ;

   SyncReset #(RSTDELAY) rstSync (.CLK(DST_CLK),
				  .IN_RST(rst),
				  .OUT_RST(OUT_RST));

   always@(posedge CLK or `BSV_RESET_EDGE RST) begin
      if (RST == `BSV_RESET_VALUE)
        rst <= `BSV_ASSIGNMENT_DELAY init ? ~ `BSV_RESET_VALUE : `BSV_RESET_VALUE;
      else
        begin
           if (ASSERT_IN)
             rst <= `BSV_ASSIGNMENT_DELAY `BSV_RESET_VALUE;
           else // if (rst == 1'b0)
             rst <= `BSV_ASSIGNMENT_DELAY ~ `BSV_RESET_VALUE;
        end // else: !if(RST == `BSV_RESET_VALUE)
   end // always@ (posedge CLK or `BSV_RESET_EDGE RST)

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial begin
      #0 ;
      rst = ~ `BSV_RESET_VALUE ;
   end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // MakeReset

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

// This is an altered version of BRAM1Load from the toolchain that removes
// some features that interfered with Yosys's ability to infer iCE40 BRAMs.


`ifdef BSV_ASSIGNMENT_DELAY
`else
 `define BSV_ASSIGNMENT_DELAY
`endif

// Single-Ported BRAM
module BRAM1Load(CLK,
                 EN,
                 WE,
                 ADDR,
                 DI,
                 DO
                 );

   parameter                      FILENAME   = "";
   parameter                      PIPELINED  = 0;
   parameter                      ADDR_WIDTH = 1;
   parameter                      DATA_WIDTH = 1;
   parameter                      MEMSIZE    = 1;
   parameter                      BINARY     = 0;

   input                          CLK;
   input                          EN;
   input                          WE;
   input [ADDR_WIDTH-1:0]         ADDR;
   input [DATA_WIDTH-1:0]         DI;
   output [DATA_WIDTH-1:0]        DO;

   reg [DATA_WIDTH-1:0]           RAM[0:MEMSIZE-1];
   reg [DATA_WIDTH-1:0]           DO_R;
   reg [DATA_WIDTH-1:0]           DO_R2;

   // synopsys translate_off
   initial
   begin : init_block
`ifdef BSV_NO_INITIAL_BLOCKS
`else
      DO_R  = { ((DATA_WIDTH+1)/2) { 2'b10 } };
      DO_R2 = { ((DATA_WIDTH+1)/2) { 2'b10 } };
`endif // !`ifdef BSV_NO_INITIAL_BLOCKS
   end
   // synopsys translate_on

   initial
   begin : init_rom_block
       if (BINARY)
           $readmemb(FILENAME, RAM, 0, MEMSIZE-1);
   end

   always @(posedge CLK) begin
      if (EN) begin
         if (WE) begin
            RAM[ADDR] <= `BSV_ASSIGNMENT_DELAY DI;
         end
         else begin
            DO_R <= `BSV_ASSIGNMENT_DELAY RAM[ADDR];
         end
      end
      DO_R2 <= `BSV_ASSIGNMENT_DELAY DO_R;
   end

   // Output driver
   assign DO = (PIPELINED) ? DO_R2 : DO_R;

endmodule // BRAM1Load

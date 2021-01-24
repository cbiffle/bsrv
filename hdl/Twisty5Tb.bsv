package Twisty5Tb;

import Assert::*;
import FShow::*;
import StmtFSM::*;

import Common::*;
import Twisty5::*;

(* synthesize *)
module mkTb ();
    let issue_wire <- mkRWire;
    Wire#(Word) response_wire <- mkDWire(?);

    let bus = (interface TwistyBus#(14);
        method Action issue(Bit#(14) address, Bool write, Word data);
            issue_wire.wset(tuple3(address, write, data));
        endmethod
        method Word response;
            return response_wire;
        endmethod
    endinterface);

    Reg#(int) cycle <- mkReg(0);
    Reg#(Bool) test_complete <- mkReg(False);
    Reg#(Maybe#(Tuple3#(Bit#(14), Bool, Word))) delayed_issue <- mkReg(tagged Invalid);

    Twisty5#(14) uut <- mkTwisty5(bus);

    rule delay_addr;
        delayed_issue <= issue_wire.wget;
    endrule

    rule show_issue;
        $display("issue = ", fshow(issue_wire.wget));
    endrule

    rule show_hart_state;
        $display("next_hart = %0d", uut.next_hart_id);
        $display("    state = ", fshow(uut.next_hart_state));
    endrule

    mkAutoFSM(seq
        action
            if (delayed_issue matches tagged Valid {0, False, .*}) noAction;
            else dynamicAssert(False, "initial fetch was bogus");
            // LUI x2, 0xDEADB000
            response_wire <= 'b1101_1110_1010_1101_1011_00010_0110111;
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {1, False, .*}) noAction;
            else dynamicAssert(False, "second fetch was bogus");
            // SW x2, (x0)
            response_wire <= 'b0000000_00010_00000_010_00000_0100011;
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {0, True, 'hDEADB000}) noAction;
            else dynamicAssert(False, "store transaction was bogus.");
        endaction
         
        test_complete <= True;
        $display("PASS");
    endseq);
endmodule

endpackage

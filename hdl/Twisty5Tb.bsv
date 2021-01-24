package Twisty5Tb;

import Assert::*;
import FShow::*;
import StmtFSM::*;

import Common::*;
import Twisty5::*;

(* synthesize *)
module mkTb ();
    let issue_wire <- mkRWire;
    Wire#(Word) response_wire <- mkWire;

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
        delay(2); // 0 -> *
        action // 1 -> 0
            if (delayed_issue matches tagged Valid {0, False, .*}) noAction;
            else dynamicAssert(False, "initial fetch was bogus");
            response_wire <= 'b1101_1110_1010_1101_1011_00010_0110111;
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {1, False, .*}) noAction;
            else dynamicAssert(False, "second fetch was bogus");
            response_wire <= 'b1101_1110_1010_1101_1011_00010_0110111;
        endaction
         
        test_complete <= True;
        $display("PASS");
    endseq);
endmodule

endpackage

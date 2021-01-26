package Twisty5Tb;

import Assert::*;
import FShow::*;
import StmtFSM::*;

import Common::*;
import Twisty5::*;

(* synthesize *)
module mkTb ();
    let issue_wire <- mkRWire;
    Wire#(Word) response_wire <- mkDWire(0);

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

    Twisty5#(14) uut <- mkTwisty5(SerialShifter, bus);

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
            // BEQ x0, x0, +32
            response_wire <= 'b0000001_00000_00000_000_0000_0_1100011;
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {8, False, .*}) noAction;
            else dynamicAssert(False, "core did not take jump");
            // ADDI x1, x0, 31
            response_wire <= 'b0000_0001_1111_00000_000_00001_0010011;
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {9, False, .*}) noAction;
            else dynamicAssert(False, "core did not continue past ADDI");
            // SW x0, (x0, 1024)
            response_wire <= 'b0100000_00000_00000_010_00000_0100011;
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {256, True, 0}) noAction;
            else dynamicAssert(False, "did not store proper value");
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {10, False, .*}) noAction;
            else dynamicAssert(False, "did not fetch insn after store");
            // SW x1, (x0, 1024)
            response_wire <= 'b0100000_00001_00000_010_00000_0100011;
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {256, True, 31}) noAction;
            else dynamicAssert(False, "did not store proper value");
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {11, False, .*}) noAction;
            else dynamicAssert(False, "did not continue after store");
            // BEQ x0, x0, -8
            response_wire <= 'b1111111_00000_00000_000_11001_1100011;
        endaction
        delay(fromInteger(valueOf(HartCount)) - 1);
        action
            if (delayed_issue matches tagged Valid {9, False, .*}) noAction;
            else dynamicAssert(False, "did not take branch back");
        endaction
         
        test_complete <= True;
        $display("PASS");
    endseq);
endmodule

endpackage

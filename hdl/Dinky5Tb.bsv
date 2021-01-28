package Dinky5Tb;

import Assert::*;
import FShow::*;
import StmtFSM::*;

import Common::*;
import Dinky5::*;

(* synthesize *)
module mkTb ();
    let issue_wire <- mkRWire;
    Wire#(Word) response_wire <- mkDWire(0);

    let bus = (interface DinkyBus;
        method issue(a, w, d) = issue_wire.wset(tuple3(a, w, d));
        method response = response_wire;
    endinterface);

    let delayed_issue <- mkRegU;
    rule delay_issue;
        delayed_issue <= issue_wire.wget;
    endrule

    Reg#(int) cycle <- mkReg(0);
    Reg#(Bool) test_complete <- mkReg(False);

    Dinky5#(14) uut <- mkDinky5(bus);

    //let insn_ADD_x1_x0_x2 = 'b0000000_00000_00001_000_00010_0110011;
    let insn_LUI_x2_DEADB000 = 'b1101_1110_1010_1101_1011_00010_0110111;
    let insn_AUIPC_x2_DEADB000 = 'b1101_1110_1010_1101_1011_00010_0010111;
    let insn_JAL_x2_8 = 'b0_0000000100_0_00000000_00010_1101111;
    let insn_JALR_x2_x2_16 = 'b0000_0001_0000_00010_000_00010_1100111;
    let insn_BEQ_x2_x2_16 = 'b0_000000_00010_00010_000_1000_0_1100011;
    let insn_LW_x3_x2_404 = 'b0100_0000_0100_00010_010_00011_0000011;

    function Stmt insn_cycle_exec_check(
        Bit#(14) pc,
        Word insn,
        Stmt check
    );
        return seq
            par
                action
                    if (delayed_issue matches tagged Valid {.a, 0, .*})
                        dynamicAssert(a == pc, "fetch of wrong address");
                    else dynamicAssert(False, "expected fetch did not happen");
                endaction
                response_wire <= insn;
                dynamicAssert(uut.core_state == onehot_state(Reg2State),
                    "reg2 state");
            endpar
            par
                dynamicAssert(uut.core_state == onehot_state(Reg1State),
                    "reg1 state");
            endpar
            par
                dynamicAssert(uut.core_state == onehot_state(ExecuteState),
                    "execute state");
                check;
            endpar
        endseq;
    endfunction

    function Stmt insn_cycle(
        Bit#(14) pc,
        Word insn
    );
        return insn_cycle_exec_check(pc, insn, (seq noAction; endseq));
    endfunction

    function Stmt insn_cycle_load(
        Bit#(14) pc,
        Word insn,
        Bit#(14) ea,
        Word loaded
    );
        return seq
            insn_cycle_exec_check(pc, insn, seq
                action
                    if (issue_wire.wget matches tagged Valid {.a, 0, .*}) 
                        dynamicAssert(a == ea, "load issued to wrong address");
                    else dynamicAssert(False, "load not issued");
                endaction
            endseq);
            par
                dynamicAssert(uut.core_state == onehot_state(LoadState),
                    "load state");
                response_wire <= loaded;
            endpar
        endseq;
    endfunction

    mkAutoFSM(seq
        insn_cycle(0, insn_LUI_x2_DEADB000);
        insn_cycle(1, insn_AUIPC_x2_DEADB000);
        insn_cycle(2, insn_JAL_x2_8);
        insn_cycle(4, insn_JALR_x2_x2_16);
        insn_cycle(7, insn_BEQ_x2_x2_16);
        insn_cycle_load(11, insn_LW_x3_x2_404, (20 + 'h404) >> 2, 'hBAADF00D);

        test_complete <= True;
        $display("PASS");
    endseq);

    (* fire_when_enabled, no_implicit_conditions *)
    rule show (!test_complete);
        cycle <= cycle + 1;
        $display("--- %0d", cycle);
        $display("state = ", fshow(uut.core_state));
        $display("inst = ", fshow(uut.core_inst));
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule show_issue (!test_complete);
        $display("issue =", fshow(issue_wire.wget));
    endrule

endmodule

endpackage

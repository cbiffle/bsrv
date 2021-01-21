package Dinky5Tb;

import Assert::*;
import FShow::*;
import StmtFSM::*;

import Dinky5::*;

(* synthesize *)
module mkTb ();
    Dinky5#(14) uut <- mkDinky5_14;

    Reg#(int) cycle <- mkReg(0);
    Reg#(Bool) test_complete <- mkReg(False);

    //let insn_ADD_x1_x0_x2 = 'b0000000_00000_00001_000_00010_0110011;
    let insn_LUI_x2_DEADB000 = 'b1101_1110_1010_1101_1011_00010_0110111;
    let insn_AUIPC_x2_DEADB000 = 'b1101_1110_1010_1101_1011_00010_0010111;
    let insn_JAL_x2_8 = 'b0_0000000100_0_00000000_00010_1101111;
    let insn_JALR_x2_x2_16 = 'b0000_0001_0000_00010_000_00010_1100111;
    let insn_BEQ_x2_x2_16 = 'b0_000000_00010_00010_000_1000_0_1100011;
    let insn_LW_x3_x2_404 = 'b0100_0000_0100_00010_010_00011_0000011;

    mkAutoFSM(seq
        par
            dynamicAssert(uut.core_state == onehot_state(FetchState), "fetch state");
            dynamicAssert(uut.mem_addr == 0,
                "core should initially fetch addr 0");
        endpar
        par
            uut.mem_result(insn_LUI_x2_DEADB000);
            dynamicAssert(uut.core_state == onehot_state(Reg2State), "reg2 state");
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(Reg1State), "reg1 state");
        endpar
        dynamicAssert(uut.core_state == onehot_state(ExecuteState), "execute state");
        par
            dynamicAssert(uut.core_state == onehot_state(FetchState), "fetch state");
            dynamicAssert(uut.mem_addr == 1,
                "core should fetch next instruction");
        endpar
        par
            uut.mem_result(insn_AUIPC_x2_DEADB000);
            dynamicAssert(uut.core_state == onehot_state(Reg2State), "reg2 state");
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(Reg1State), "reg1 state");
        endpar
        dynamicAssert(uut.core_state == onehot_state(ExecuteState), "execute state");
        par
            dynamicAssert(uut.core_state == onehot_state(FetchState), "fetch state");
            dynamicAssert(uut.mem_addr == 2,
                "core should fetch next instruction");
        endpar
        par
            uut.mem_result(insn_JAL_x2_8);
            dynamicAssert(uut.core_state == onehot_state(Reg2State), "reg2 state");
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(Reg1State), "reg1 state");
        endpar
        dynamicAssert(uut.core_state == onehot_state(ExecuteState), "execute state");
        par
            dynamicAssert(uut.core_state == onehot_state(FetchState), "fetch state");
            dynamicAssert(uut.mem_addr == 4,
                "core should follow jump");
        endpar
        par
            uut.mem_result(insn_JALR_x2_x2_16);
            dynamicAssert(uut.core_state == onehot_state(Reg2State), "reg2 state");
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(Reg1State), "reg1 state");
        endpar
        dynamicAssert(uut.core_state == onehot_state(ExecuteState), "execute state");
        par
            dynamicAssert(uut.core_state == onehot_state(FetchState), "fetch state");
            $display(fshow(uut.mem_addr));
            dynamicAssert(uut.mem_addr == 7,
                "core should follow jump");
        endpar
        par
            uut.mem_result(insn_BEQ_x2_x2_16);
            dynamicAssert(uut.core_state == onehot_state(Reg2State), "reg2 state");
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(Reg1State), "reg1 state");
        endpar
        dynamicAssert(uut.core_state == onehot_state(ExecuteState), "execute state");
        par
            dynamicAssert(uut.core_state == onehot_state(FetchState), "fetch state");
            dynamicAssert(uut.mem_addr == 11,
                "core should follow jump");
        endpar

        par
            uut.mem_result(insn_LW_x3_x2_404);
            dynamicAssert(uut.core_state == onehot_state(Reg2State), "reg2 state");
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(Reg1State), "reg1 state");
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(ExecuteState), "execute state");
            dynamicAssert(uut.mem_addr == (20 + 'h404) >> 2, "load EA");
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(LoadState), "load state");
            uut.mem_result('hBEEF_D00D);
        endpar
        par
            dynamicAssert(uut.core_state == onehot_state(FetchState), "fetch state");
            dynamicAssert(uut.mem_addr == 12, "sequential ex");
        endpar
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
    rule show_memaddr (!test_complete);
        $display("MA = %0h", uut.mem_addr);
    endrule

endmodule

endpackage

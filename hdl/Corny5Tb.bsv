package Corny5Tb;

import Assert::*;
import FShow::*;
import StmtFSM::*;

import Common::*;
import Corny5::*;

(* synthesize *)
module mkTb ();
    Corny5#(14) uut <- mkCorny5;

    Reg#(int) cycle <- mkReg(0);
    Reg#(Bool) test_complete <- mkReg(False);
    Reg#(Bit#(14)) delayed_addr <- mkRegU;

    rule delay_addr;
        delayed_addr <= uut.bus.mem_addr;
    endrule

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
                dynamicAssert(delayed_addr == pc, "fetch PC");
                uut.bus.mem_result(insn);
                dynamicAssert(uut.core_state == RegState,
                    "reg state");
            endpar
            par
                dynamicAssert(uut.core_state == ExecuteState,
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
                dynamicAssert(uut.bus.mem_addr == ea, "load EA");
            endseq);
            par
                dynamicAssert(uut.core_state == LoadState,
                    "load state");
                uut.bus.mem_result(loaded);
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
    rule show_memaddr (!test_complete);
        $display("MA = %0h", uut.bus.mem_addr);
    endrule

endmodule

endpackage

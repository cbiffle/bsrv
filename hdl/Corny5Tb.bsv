package Corny5Tb;

import Assert::*;
import FShow::*;
import StmtFSM::*;

import Common::*;
import TestUtil::*;
import Corny5::*;

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

    Corny5#(14) uut <- mkCorny5(bus);

    function Stmt insn_cycle(
        Bit#(14) pc,
        Word insn,
        Action check
    );
        return seq
            par
                action
                    if (delayed_issue matches tagged Valid {.a, False, .*})
                        dynamicAssert(a == pc, "fetch of wrong PC");
                    else dynamicAssert(False, "did not fetch");
                endaction
                response_wire <= insn;
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

    function Action check_rf_write(RegId r, Word value);
        action
            if (uut.rf_write_snoop matches tagged Valid {.i, .x}) begin
                $display("RF WRITE r%0d <= %0h", i, x);
                dynamicAssert(i == r, "value written to wrong register");
                dynamicAssert(x == value, "wrong value written to regfile");
            end else dynamicAssert(False, "expected RF write did not occur");
        endaction
    endfunction

    function Action rf_not_written;
        action
            if (uut.rf_write_snoop matches tagged Valid {.i, .x}) begin
                $display("UNEXPECTED WRITE r%0d <= %0h", i, x);
                dynamicAssert(False, "RF written unexpectedly");
            end
        endaction
    endfunction

    function Stmt insn_cycle_load(
        Bit#(14) pc,
        Word insn,
        Bit#(14) ea,
        Word loaded
    );
        return seq
            insn_cycle(pc, insn, action
                if (issue_wire.wget matches tagged Valid {.a, False, .*})
                    dynamicAssert(a == ea, "loaded wrong address");
                else dynamicAssert(False, "did not load");
            endaction);
            par
                dynamicAssert(uut.core_state == LoadState, "not in load state");
                response_wire <= loaded;
                check_rf_write(insn[11:7], loaded);
            endpar
        endseq;
    endfunction

    function Stmt insn_cycle_store(
        Bit#(14) pc,
        Word insn,
        Bit#(14) ea,
        Word stored
    );
        return seq
            insn_cycle(pc, insn, action
                if (issue_wire.wget matches tagged Valid {.a, True, .d}) begin
                    dynamicAssert(a == ea, "stored wrong address");
                    dynamicAssert(d == stored, "stored wrong value");
                end else dynamicAssert(False, "did not store");
                rf_not_written;
            endaction);
            par
                dynamicAssert(uut.core_state == JustFetchState, "not fetching");
            endpar
        endseq;
    endfunction

    Word lhs = 'h89ABCDEF;
    Word rhs = 'h01234567;
    mkAutoFSM(seq
        insn_cycle(0, rv32_lui(2, 'hDEADB),
            check_rf_write(2, 'hDEADB000));
        insn_cycle(1, rv32_auipc(2, 'hDEADB),
            check_rf_write(2, 'hDEADB000 + 4));
        insn_cycle(2, rv32_jal(2, 8),
            check_rf_write(2, 3 * 4));
        insn_cycle(4, rv32_jalr(2, 2, 16),
            check_rf_write(2, 5 * 4));
        insn_cycle(7, rv32_b(CondEQ, 2, 2, 16),
            rf_not_written);
        insn_cycle_load(11, rv32_lw(3, 2, 'h404), (20 + 'h404) >> 2, 'hBAADF00D);
        insn_cycle_store(12, rv32_sw(3, 2, 'h404), (20 + 'h404) >> 2, 'hBAADF00D);

        insn_cycle(13, rv32_addi(2, 3, 42), check_rf_write(2, 'hBAADF00D + 42));

        insn_cycle(14, rv32_slti(1, 0, 42), check_rf_write(1, 1));
        insn_cycle(15, rv32_sltiu(1, 0, 42), check_rf_write(1, 1));
        insn_cycle(16, rv32_slti(1, 2, 42), check_rf_write(1, 1));
        insn_cycle(17, rv32_sltiu(1, 2, 42), check_rf_write(1, 0));

        insn_cycle(18, rv32_xori(2, 2, 'hae9), check_rf_write(2, 'h45520ADE));
        insn_cycle(19, rv32_andi(2, 2, 'hF00), check_rf_write(2, 'h45520A00));
        insn_cycle(20, rv32_ori(2, 2, 'h0AD), check_rf_write(2, 'h45520AAD));

        insn_cycle(21, rv32_xori(2, 2, 'hFFF), check_rf_write(2, 'hBAADF552));
        insn_cycle(22, rv32_slli(3, 2, 12), check_rf_write(3, 'hDF552000));
        insn_cycle(23, rv32_srli(3, 2, 12), check_rf_write(3, 'h000BAADF));
        insn_cycle(24, rv32_srai(3, 2, 12), check_rf_write(3, 'hFFFBAADF));

        // Get some unusual constants into registers.
        insn_cycle(25, rv32_lui(1, 'h76543), noAction);
        insn_cycle(26, rv32_xori(1, 1, 'hDEF), noAction); // = 89ABCDEF
        insn_cycle(27, rv32_lui(2, 'h01234), noAction);
        insn_cycle(28, rv32_ori(2, 2, 'h567), noAction); // = 01234567

        // ALU reg ops
        insn_cycle(29, rv32_add(3, 1, 2), check_rf_write(3, lhs + rhs));
        insn_cycle(30, rv32_sub(3, 1, 2), check_rf_write(3, lhs - rhs));
        insn_cycle(31, rv32_and(3, 1, 2), check_rf_write(3, lhs & rhs));
        insn_cycle(32, rv32_or(3, 1, 2), check_rf_write(3, lhs | rhs));
        insn_cycle(33, rv32_xor(3, 1, 2), check_rf_write(3, lhs ^ rhs));
        insn_cycle(34, rv32_slt(3, 1, 2), check_rf_write(3, 1));
        insn_cycle(35, rv32_slt(3, 2, 1), check_rf_write(3, 0));
        insn_cycle(36, rv32_sltu(3, 1, 2), check_rf_write(3, 0));
        insn_cycle(37, rv32_sltu(3, 2, 1), check_rf_write(3, 1));
        insn_cycle(38, rv32_sll(3, 1, 2), check_rf_write(3, lhs << rhs[4:0]));
        insn_cycle(39, rv32_srl(3, 1, 2), check_rf_write(3, lhs >> rhs[4:0]));
        insn_cycle(40, rv32_sra(3, 1, 2), check_rf_write(3, {-1, lhs[31:7]}));

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
        $display("issue = ", fshow(issue_wire.wget));
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule show_rf_writes (uut.rf_write_snoop matches tagged Valid {.i, .x});
        $display("RF WRITE r%0d <= %0h", i, x);
    endrule
endmodule

endpackage

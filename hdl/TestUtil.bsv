package TestUtil;

import Common::*;

///////////////////////////////////////////////////////////////////////////////
// Little RV32I "assembler"

typedef enum {
    CondEQ = 3'b000,
    CondNE = 3'b001,
    CondLT = 3'b100,
    CondGE = 3'b101,
    CondLTU = 3'b110,
    CondGEU = 3'b111
} BranchCondition deriving (Eq, FShow, Bits);

function Word rv32_lui(RegId rd, Bit#(20) immed20) = {immed20, rd, 7'b0110111};
function Word rv32_auipc(RegId rd, Bit#(20) immed20) = {immed20, rd, 7'b0010111};
function Word rv32_jal(RegId rd, Bit#(21) d) =
    {d[20], d[10:1], d[11], d[19:12], rd, 7'b1101111};
function Word rv32_jalr(RegId rd, RegId rs1, Bit#(12) d) =
    {d, rs1, 3'b000, rd, 7'b1100111};
function Word rv32_b(BranchCondition cc, RegId rs1, RegId rs2, Bit#(13) d) =
    {d[12], d[10:5], rs2, rs1, pack(cc), d[4:1], d[11], 7'b1100011};
function Word rv32_lw(RegId rd, RegId rs1, Bit#(12) d) =
    {d, rs1, 3'b010, rd, 7'b0000011};
function Word rv32_lb(RegId rd, RegId rs1, Bit#(12) d) =
    {d, rs1, 3'b000, rd, 7'b0000011};
function Word rv32_lbu(RegId rd, RegId rs1, Bit#(12) d) =
    {d, rs1, 3'b100, rd, 7'b0000011};
function Word rv32_lh(RegId rd, RegId rs1, Bit#(12) d) =
    {d, rs1, 3'b001, rd, 7'b0000011};
function Word rv32_lhu(RegId rd, RegId rs1, Bit#(12) d) =
    {d, rs1, 3'b101, rd, 7'b0000011};
function Word rv32_sw(RegId rs2, RegId rs1, Bit#(12) d) =
    {d[11:5], rs2, rs1, 3'b010, d[4:0], 7'b0100011};

function Word rv32_alu_imm(Bit#(3) op, RegId rd, RegId rs1, Bit#(12) d) =
    {d[11:0], rs1, op, rd, 7'b0010011};

function Word rv32_addi(RegId rd, RegId rs1, Bit#(12) d) =
    rv32_alu_imm('b000, rd, rs1, d);
function Word rv32_slti(RegId rd, RegId rs1, Bit#(12) d) =
    rv32_alu_imm('b010, rd, rs1, d);
function Word rv32_sltiu(RegId rd, RegId rs1, Bit#(12) d) =
    rv32_alu_imm('b011, rd, rs1, d);
function Word rv32_xori(RegId rd, RegId rs1, Bit#(12) d) =
    rv32_alu_imm('b100, rd, rs1, d);
function Word rv32_ori(RegId rd, RegId rs1, Bit#(12) d) =
    rv32_alu_imm('b110, rd, rs1, d);
function Word rv32_andi(RegId rd, RegId rs1, Bit#(12) d) =
    rv32_alu_imm('b111, rd, rs1, d);

function Word rv32_slli(RegId rd, RegId rs1, Bit#(5) d) =
    rv32_alu_imm('b001, rd, rs1, {'b0000000, d});
function Word rv32_srli(RegId rd, RegId rs1, Bit#(5) d) =
    rv32_alu_imm('b101, rd, rs1, {'b0000000, d});
function Word rv32_srai(RegId rd, RegId rs1, Bit#(5) d) =
    rv32_alu_imm('b101, rd, rs1, {'b0100000, d});

function Word rv32_alu_reg(Bit#(3) op, bit f7, RegId rd, RegId rs1, RegId rs2) =
    {0, f7, 5'b0, rs2, rs1, op, rd, 7'b0110011};

function Word rv32_add(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b000, 0, rd, rs1, rs2);
function Word rv32_sub(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b000, 1, rd, rs1, rs2);
function Word rv32_slt(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b010, 0, rd, rs1, rs2);
function Word rv32_sltu(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b011, 0, rd, rs1, rs2);
function Word rv32_xor(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b100, 0, rd, rs1, rs2);
function Word rv32_or(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b110, 0, rd, rs1, rs2);
function Word rv32_and(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b111, 0, rd, rs1, rs2);

function Word rv32_sll(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b001, 0, rd, rs1, rs2);
function Word rv32_srl(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b101, 0, rd, rs1, rs2);
function Word rv32_sra(RegId rd, RegId rs1, RegId rs2) =
    rv32_alu_reg('b101, 1, rd, rs1, rs2);

endpackage

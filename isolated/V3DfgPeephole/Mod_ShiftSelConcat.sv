module Mod_ShiftSelConcat (
    input wire in_cond_sel,
    input wire [7:0] in_narrow,
    input wire [7:0] in_repl_src,
    input wire [2:0] in_sel_lsb,
    input wire [2:0] in_sel_lsb2,
    input wire [3:0] in_shift_amount,
    input wire [15:0] in_wide,
    output logic [15:0] out_concat,
    output logic [7:0] out_concat_adj_sels,
    output logic [15:0] out_concat_nested_adj_sels_lhs,
    output logic [15:0] out_concat_nested_adj_sels_rhs,
    output logic [15:0] out_concat_nots,
    output logic [15:0] out_concat_zero_shift_l,
    output logic [7:0] out_concat_zero_shift_r,
    output logic [7:0] out_replicate_once,
    output logic [7:0] out_sel_basic,
    output logic [7:0] out_sel_from_concat_lhs,
    output logic [3:0] out_sel_from_concat_rhs,
    output logic [7:0] out_sel_from_cond,
    output logic [4:0] out_sel_from_not,
    output logic [7:0] out_sel_from_replicate,
    output logic [3:0] out_sel_from_sel,
    output logic [7:0] out_sel_from_shiftl,
    output logic [7:0] out_sel_straddle_concat,
    output logic [15:0] out_shift_l,
    output logic [15:0] out_shift_r,
    output logic [7:0] out_shift_rhs_zext,
    output logic [15:0] out_shift_rs
);
    logic [15:0] intermediate_concat_straddle;
    logic [7:0] intermediate_not_src;
    logic [15:0] intermediate_concat_nots;
    logic [7:0] intermediate_concat_adj_sels_part1;
    logic [7:0] intermediate_concat_adj_sels_part2;
    logic [7:0] intermediate_nested_concat_adj_lhs;
    logic [15:0] intermediate_nested_concat_lhs;
    logic [7:0] intermediate_nested_concat_adj_rhs;
    logic [15:0] intermediate_nested_concat_rhs;
    logic [4:0] intermediate_zext_4 = 5'b0;
    logic [8:0] intermediate_zext_8_ext = 9'b0;
    logic [15:0] intermediate_cond_source;
    parameter [15:0] CONST_WIDE_1 = 16'h0001;
    parameter [15:0] CONST_WIDE_2 = 16'h0002;
    logic [15:0] temp_shift_l_for_sel;
    logic [12:0] intermediate_shift_zext_rhs_src;
    always_comb begin
        intermediate_cond_source = in_cond_sel ? CONST_WIDE_1 : CONST_WIDE_2;
        out_sel_from_cond = intermediate_cond_source[7:0];
        out_shift_l = in_wide << in_shift_amount;
        out_shift_r = in_wide >> in_shift_amount;
        out_shift_rs = in_wide >>> in_shift_amount;
        intermediate_shift_zext_rhs_src = {intermediate_zext_4, in_narrow};
        out_shift_rhs_zext = in_wide >> intermediate_shift_zext_rhs_src;
        out_sel_basic = in_wide[7:0];
        intermediate_concat_straddle = {in_narrow, in_narrow};
        out_sel_from_concat_rhs = intermediate_concat_straddle[3:0];
        out_sel_from_concat_lhs = intermediate_concat_straddle[15:8];
        out_sel_straddle_concat = intermediate_concat_straddle[11:4];
        out_sel_from_replicate = {2{in_repl_src}}[in_sel_lsb + 1 +: 8];
        intermediate_not_src = ~in_narrow;
        out_sel_from_not = intermediate_not_src[in_sel_lsb2 +: 5];
        out_sel_from_sel = in_wide[7:0][3:0];
        temp_shift_l_for_sel = in_wide << in_shift_amount;
        out_sel_from_shiftl = temp_shift_l_for_sel[7:0];
        out_concat = {in_wide[7:0], in_wide[15:8]};
        intermediate_concat_nots = {~in_wide[7:0], ~in_wide[15:8]};
        out_concat_nots = intermediate_concat_nots;
        intermediate_concat_adj_sels_part1 = in_narrow[7:4];
        intermediate_concat_adj_sels_part2 = in_narrow[3:0];
        out_concat_adj_sels = {intermediate_concat_adj_sels_part1, intermediate_concat_adj_sels_part2};
        intermediate_nested_concat_adj_lhs = {in_narrow[7:4], in_narrow[3:0]};
        intermediate_nested_concat_lhs = {intermediate_nested_concat_adj_lhs, in_wide[7:0]};
        out_concat_nested_adj_sels_lhs = intermediate_nested_concat_lhs;
        intermediate_nested_concat_adj_rhs = {in_narrow[7:4], in_narrow[3:0]};
        intermediate_nested_concat_rhs = {in_wide[7:0], intermediate_nested_concat_adj_rhs};
        out_concat_nested_adj_sels_rhs = intermediate_nested_concat_rhs;
        out_concat_zero_shift_r = {intermediate_zext_4[3:0], in_narrow[7:4]};
        out_concat_zero_shift_l = {in_wide[7:0], intermediate_zext_8_ext[7:0]};
        out_replicate_once = {1{in_narrow}};
    end
endmodule


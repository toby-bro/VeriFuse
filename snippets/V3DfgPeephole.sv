module Mod_BasicOps (
    input wire [7:0] in_a,
    input wire [7:0] in_b,
    input wire [7:0] in_c,
    input wire [7:0] in_const1,
    input wire [7:0] in_const2,
    input wire [0:0] in_bit,
    output logic [7:0] out_arith,
    output logic [7:0] out_bitwise,
    output logic [0:0] out_logical,
    output logic [7:0] out_unary_not,
    output logic [7:0] out_negate,
    output logic [7:0] out_add_assoc,
    output logic [7:0] out_mul_assoc,
    output logic [7:0] out_and_assoc,
    output logic [7:0] out_or_assoc,
    output logic [7:0] out_xor_assoc,
    output logic [7:0] out_and_swap_const,
    output logic [7:0] out_or_swap_not,
    output logic [7:0] out_xor_swap_var
);
    logic [7:0] intermediate_arith;
    logic [7:0] intermediate_bitwise;
    logic [0:0] intermediate_logical;
    logic [7:0] intermediate_add_assoc;
    logic [7:0] intermediate_mul_assoc;
    logic [7:0] intermediate_and_assoc;
    logic [7:0] intermediate_or_assoc;
    logic [7:0] intermediate_xor_assoc;
    parameter [7:0] CONST_ZERO = 8'h00;
    always_comb begin
        intermediate_arith = in_a;
        intermediate_arith = intermediate_arith + in_b;
        intermediate_arith = intermediate_arith - in_c;
        intermediate_arith = intermediate_arith * in_const1;
        if (in_b != CONST_ZERO) begin
            intermediate_arith = intermediate_arith / in_b;
            intermediate_arith = intermediate_arith % in_b;
        end else begin
            intermediate_arith = 'x;
        end
        out_arith = intermediate_arith;
        intermediate_bitwise = in_a;
        intermediate_bitwise = intermediate_bitwise & in_b;
        intermediate_bitwise = intermediate_bitwise | in_c;
        intermediate_bitwise = intermediate_bitwise ^ in_const1;
        out_bitwise = intermediate_bitwise;
        intermediate_logical = (in_a != CONST_ZERO) && (in_b != CONST_ZERO);
        intermediate_logical = intermediate_logical || (in_c != CONST_ZERO);
        out_logical = !intermediate_logical;
        out_unary_not = ~in_a;
        out_negate = -in_a;
        intermediate_add_assoc = (in_a + in_b) + in_c;
        out_add_assoc = intermediate_add_assoc;
        intermediate_mul_assoc = (in_a * in_b) * in_c;
        out_mul_assoc = intermediate_mul_assoc;
        intermediate_and_assoc = (in_a & in_b) & in_c;
        out_and_assoc = intermediate_and_assoc;
        intermediate_or_assoc = (in_a | in_b) | in_c;
        out_or_assoc = intermediate_or_assoc;
        intermediate_xor_assoc = (in_a ^ in_b) ^ in_c;
        out_xor_assoc = intermediate_xor_assoc;
        out_and_swap_const = in_const1 & in_a;
        out_or_swap_not = (~in_a) | in_b;
        out_xor_swap_var = in_b ^ in_c;
    end
endmodule
module Mod_ShiftSelConcat (
    input wire [15:0] in_wide,
    input wire [7:0] in_narrow,
    input wire [3:0] in_shift_amount,
    input wire [2:0] in_sel_lsb,
    input wire [2:0] in_sel_lsb2,
    input wire [7:0] in_repl_src,
    input wire [0:0] in_cond_sel,
    output logic [15:0] out_shift_l,
    output logic [15:0] out_shift_r,
    output logic [15:0] out_shift_rs,
    output logic [7:0] out_sel_basic,
    output logic [3:0] out_sel_from_concat_rhs,
    output logic [7:0] out_sel_from_concat_lhs,
    output logic [7:0] out_sel_straddle_concat,
    output logic [7:0] out_sel_from_replicate,
    output logic [4:0] out_sel_from_not,
    output logic [3:0] out_sel_from_sel,
    output logic [7:0] out_sel_from_cond,
    output logic [7:0] out_sel_from_shiftl,
    output logic [15:0] out_concat,
    output logic [15:0] out_concat_nots,
    output logic [7:0] out_concat_adj_sels,
    output logic [15:0] out_concat_nested_adj_sels_lhs,
    output logic [15:0] out_concat_nested_adj_sels_rhs,
    output logic [7:0] out_concat_zero_shift_r,
    output logic [15:0] out_concat_zero_shift_l,
    output logic [7:0] out_replicate_once,
    output logic [7:0] out_shift_rhs_zext
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
module Mod_ReductionOneHot (
    input wire [7:0] in_vec,
    input wire [0:0] in_bit,
    input wire [7:0] in_vec_a,
    input wire [7:0] in_vec_b,
    input wire [0:0] in_cond,
    input wire [7:0] in_red_concat_lhs,
    output logic [0:0] out_red_or,
    output logic [0:0] out_red_and,
    output logic [0:0] out_red_xor,
    output logic [0:0] out_red_bit,
    output logic [0:0] out_red_concat,
    output logic [0:0] out_red_cond,
    output logic [0:0] out_or_red,
    output logic [7:0] out_onehot,
    output logic [7:0] out_onehot0,
    output logic [3:0] out_countones,
    output logic [3:0] out_clog2
);
    logic [15:0] intermediate_red_concat_src;
    logic [7:0] intermediate_red_cond_then;
    logic [7:0] intermediate_red_cond_else;
    logic [7:0] intermediate_red_cond_src;
    logic [0:0] intermediate_red_a;
    logic [0:0] intermediate_red_b;
    parameter [7:0] CONST_ZERO_8 = 8'h00;
    parameter [7:0] CONST_ONES_8 = 8'hFF;
    always_comb begin
        intermediate_red_cond_then = in_vec_a;
        intermediate_red_cond_else = CONST_ZERO_8;
        intermediate_red_cond_src = in_cond ? intermediate_red_cond_then : intermediate_red_cond_else;
        out_red_cond = |intermediate_red_cond_src;
        intermediate_red_a = |in_vec_a;
        intermediate_red_b = |in_vec_b;
        out_or_red = intermediate_red_a | intermediate_red_b;
        out_red_or = |in_vec;
        out_red_and = &in_vec;
        out_red_xor = ^in_vec;
        out_red_bit = |in_bit;
        intermediate_red_concat_src = {in_red_concat_lhs, CONST_ONES_8};
        out_red_concat = |intermediate_red_concat_src;
        out_onehot = $onehot(in_vec);
        out_onehot0 = $onehot0(in_vec);
        out_countones = $countones(in_vec);
        if (|in_vec)
            out_clog2 = $clog2(in_vec);
        else
            out_clog2 = 'x;
    end
endmodule
module Mod_TernaryLogic (
    input wire [7:0] in_a,
    input wire [7:0] in_b,
    input wire [7:0] in_c,
    input wire [0:0] in_cond,
    input wire [0:0] in_cond_not,
    input wire [0:0] in_cond_neq_lhs,
    input wire [0:0] in_cond_neq_rhs,
    input wire [7:0] in_not_then,
    input wire [7:0] in_not_else,
    input wire [0:0] in_bit,
    output logic [0:0] out_eq,
    output logic [0:0] out_neq,
    output logic [0:0] out_gt,
    output logic [0:0] out_lt,
    output logic [0:0] out_gte,
    output logic [0:0] out_lte,
    output logic [0:0] out_eq_concat,
    output logic [0:0] out_ternary,
    output logic [0:0] out_ternary_const_cond_true,
    output logic [0:0] out_ternary_const_cond_false,
    output logic [0:0] out_ternary_swapped_cond,
    output logic [0:0] out_ternary_swapped_neq_cond,
    output logic [7:0] out_ternary_pulled_nots,
    output logic [7:0] out_ternary_inc,
    output logic [7:0] out_ternary_dec,
    output logic [0:0] out_ternary_1bit_0then,
    output logic [0:0] out_ternary_1bit_1then,
    output logic [0:0] out_ternary_1bit_0else,
    output logic [0:0] out_ternary_1bit_1else,
    output logic [0:0] out_not_eq,
    output logic [0:0] out_not_neq
);
    parameter [7:0] CONST_ONE_8 = 8'h01;
    parameter [0:0] CONST_ZERO_1 = 1'b0;
    parameter [0:0] CONST_ONE_1 = 1'b1;
    logic [7:0] intermediate_const_concat_comp;
    logic [15:0] intermediate_concat_comp_src;
    always_comb begin
        out_eq = (in_a == in_b);
        out_neq = (in_a != in_b);
        out_gt = (in_a > in_b);
        out_lt = (in_a < in_b);
        out_gte = (in_a >= in_b);
        out_lte = (in_a <= in_b);
        out_not_eq = !(in_a == in_b);
        out_not_neq = !(in_a != in_b);
        intermediate_const_concat_comp = 8'hAA;
        intermediate_concat_comp_src = {in_a, in_b};
        out_eq_concat = (intermediate_const_concat_comp == intermediate_concat_comp_src[7:0]);
        out_ternary = in_cond ? in_a[0] : in_b[0];
        out_ternary_const_cond_true = 1'b1 ? in_a[0] : in_b[0];
        out_ternary_const_cond_false = 1'b0 ? in_a[0] : in_b[0];
        out_ternary_swapped_cond = !in_cond_not ? in_a[0] : in_b[0];
        out_ternary_swapped_neq_cond = (in_cond_neq_lhs != in_cond_neq_rhs) ? in_a[0] : in_b[0];
        out_ternary_pulled_nots = in_cond ? ~in_not_then : ~in_not_else;
        out_ternary_inc = in_cond ? (in_a + CONST_ONE_8) : in_a;
        out_ternary_dec = in_cond ? (in_a - CONST_ONE_8) : in_a;
        out_ternary_1bit_0then = in_cond ? CONST_ZERO_1 : in_bit;
        out_ternary_1bit_1then = in_cond ? CONST_ONE_1 : in_bit;
        out_ternary_1bit_0else = in_cond ? in_bit : CONST_ZERO_1;
        out_ternary_1bit_1else = in_cond ? in_bit : CONST_ONE_1;
    end
endmodule
module Mod_ArrayOps (
    input wire [7:0] in_data,
    input wire [1:0] in_index,
    input wire [1:0] in_const_index,
    output logic [7:0] out_array_sel_var,
    output logic [7:0] out_array_sel_const
);
    logic [7:0] my_array [3:0];
    always_comb begin
        my_array[0] = in_data;
        my_array[1] = in_data + 8'd1;
        my_array[2] = in_data + 8'd2;
        my_array[3] = in_data + 8'd3;
        out_array_sel_var = my_array[in_index];
        out_array_sel_const = my_array[in_const_index];
    end
endmodule
module Mod_SignedOps (
    input wire signed [7:0] in_sa,
    input wire signed [7:0] in_sb,
    input wire [7:0] in_u,
    input wire signed [3:0] in_shift_sa,
    input wire [3:0] in_shift_u,
    input wire signed [3:0] in_narrow_sa,
    output logic signed [7:0] out_sdiv,
    output logic signed [7:0] out_smod,
    output logic signed [7:0] out_smul,
    output logic [0:0] out_sgt,
    output logic [0:0] out_slt,
    output logic [0:0] out_sgte,
    output logic [0:0] out_slte,
    output logic signed [7:0] out_shift_rs_signed,
    output logic signed [7:0] out_sext,
    output logic signed [7:0] out_pow_ss,
    output logic signed [7:0] out_pow_su,
    output logic [7:0] out_pow_us
);
    logic signed [7:0] intermediate_sdiv;
    logic signed [7:0] intermediate_smod;
    always_comb begin
        if (in_sb != 8'd0) begin
            intermediate_sdiv = in_sa / in_sb;
            intermediate_smod = in_sa % in_sb;
        end else begin
            intermediate_sdiv = 'x;
            intermediate_smod = 'x;
        end
        out_sdiv = intermediate_sdiv;
        out_smod = intermediate_smod;
        out_smul = in_sa * in_sb;
        out_sgt = (in_sa > in_sb);
        out_slt = (in_sa < in_sb);
        out_sgte = (in_sa >= in_sb);
        out_slte = (in_sa <= in_sb);
        out_shift_rs_signed = in_sa >>> in_shift_u;
        out_sext = $signed(in_narrow_sa);
        out_pow_ss = in_sa ** in_shift_sa;
        out_pow_su = in_sa ** in_shift_u;
        out_pow_us = in_u ** in_shift_sa;
    end
endmodule

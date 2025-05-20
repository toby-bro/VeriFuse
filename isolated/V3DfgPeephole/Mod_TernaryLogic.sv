module Mod_TernaryLogic (
    input wire [7:0] in_not_else,
    output logic [7:0] out_ternary_inc,
    output logic out_ternary,
    output logic out_ternary_1bit_1else,
    output logic out_not_eq,
    output logic out_lte,
    input wire [7:0] in_a,
    output logic out_lt,
    output logic [7:0] out_ternary_dec,
    output logic out_ternary_swapped_neq_cond,
    output logic out_gt,
    input wire in_bit,
    output logic out_eq_concat,
    input wire [7:0] in_c,
    output logic out_ternary_1bit_1then,
    input wire [7:0] in_not_then,
    output logic out_neq,
    input wire in_cond_neq_lhs,
    output logic out_gte,
    output logic out_ternary_1bit_0then,
    output logic [7:0] out_ternary_pulled_nots,
    input wire in_cond_not,
    output logic out_not_neq,
    output logic out_ternary_const_cond_true,
    output logic out_ternary_const_cond_false,
    input wire in_cond,
    output logic out_ternary_1bit_0else,
    input wire [7:0] in_b,
    output logic out_ternary_swapped_cond,
    output logic out_eq,
    input wire in_cond_neq_rhs
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


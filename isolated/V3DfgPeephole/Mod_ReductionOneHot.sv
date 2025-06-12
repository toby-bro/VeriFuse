module Mod_ReductionOneHot (
    output logic out_red_and,
    output logic out_or_red,
    output logic [7:0] out_onehot0,
    input wire [7:0] in_vec,
    output logic out_red_bit,
    input wire [7:0] in_vec_a,
    input wire [7:0] in_red_concat_lhs,
    output logic out_red_cond,
    output logic out_red_or,
    output logic [3:0] out_countones,
    input wire in_cond,
    input wire [7:0] in_vec_b,
    output logic out_red_xor,
    input wire in_bit,
    output logic out_red_concat,
    output logic [7:0] out_onehot,
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


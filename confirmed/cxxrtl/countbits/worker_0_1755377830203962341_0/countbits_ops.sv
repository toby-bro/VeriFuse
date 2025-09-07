module CombinationalLogicImplicit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [3:0] sum
);
    always @* begin
        sum = a + b;
    end
endmodule

module ComplexConversions (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [15:0] out_concat
);
    always_comb begin
        out_concat = {in_a, in_b};
    end
endmodule

module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module recursive_param_diag_mod (
    input int dummy_in,
    output int out_val
);
    assign out_val = dummy_in;
endmodule

module sequential_always_assign (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule

module split_for_loop (
    input logic clk_i,
    input logic [7:0] start_val_i,
    output logic [15:0] sum_out_i
);
    always @(posedge clk_i) begin
        sum_out_i <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            sum_out_i <= sum_out_i + start_val_i + i;
        end
    end
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic [3:0] inj_a_1755377830490_312,
    input logic inj_a_1755377830492_285,
    input logic [3:0] inj_b_1755377830490_364,
    input logic inj_b_1755377830492_365,
    input logic [1:0] inj_case_expr_1755377830490_540,
    input int inj_dummy_in_1755377830763_153,
    input bit inj_enable_in_1755377830528_286,
    input logic [7:0] inj_in_a_1755377830531_804,
    input wire rst,
    output logic [3:0] cnt,
    output logic [4:0] inj_internal_out_1755377830490_785,
    output logic [4:0] inj_internal_out_1755377831049_504,
    output bit inj_out_1755377830528_293,
    output logic [7:0] inj_out_1755377831208_1,
    output logic inj_out_a_1755377830867_226,
    output int inj_out_b_1755377830867_326,
    output logic [15:0] inj_out_concat_1755377830531_635,
    output reg inj_out_res_1755377830620_21,
    output logic [7:0] inj_out_sum_m1_1755377830614_891,
    output int inj_out_val_1755377830763_115,
    output logic inj_q_out_1755377830519_395,
    output logic [3:0] inj_sum_1755377830490_590,
    output logic inj_sum_1755377830492_554,
    output logic [15:0] inj_sum_out_i_1755377830637_404,
    output logic [7:0] inj_var_out_m1_1755377830614_259
);
    // BEGIN: case_priority_overlapping_mod_ts1755377830490
    // BEGIN: simple_adder_ts1755377830492
    // BEGIN: LogicDependencyChain_ts1755377830519
    logic q1_ts1755377830519, q2_ts1755377830519;
        // BEGIN: expr_preadd_comb_ts1755377830614
        logic [7:0] var_m1_ts1755377830614;
            sequential_always_assign sequential_always_assign_inst_1755377831208_2049 (
                .in(var_m1_ts1755377830614),
                .out(inj_out_1755377831208_1),
                .clk(clk)
            );
            // BEGIN: case_unique_casez_reordered_mod_ts1755377831049
            always @* begin
                unique casez ({inj_case_expr_1755377830490_540[0], inj_a_1755377830490_312[3:2], inj_case_expr_1755377830490_540[1]})
                    4'b1?0?: inj_internal_out_1755377831049_504 = 30;
                    4'b?101: inj_internal_out_1755377831049_504 = 31;  
                    4'b0?1?: inj_internal_out_1755377831049_504 = 32;
                    4'b1?1?: inj_internal_out_1755377831049_504 = 33;  
                    4'b?111: inj_internal_out_1755377831049_504 = 34;  
                endcase
            end
            // END: case_unique_casez_reordered_mod_ts1755377831049

            ModuleBasic ModuleBasic_inst_1755377830867_5062 (
                .a(q1_ts1755377830519),
                .b(inj_dummy_in_1755377830763_153),
                .out_a(inj_out_a_1755377830867_226),
                .out_b(inj_out_b_1755377830867_326)
            );
            recursive_param_diag_mod recursive_param_diag_mod_inst_1755377830763_4467 (
                .dummy_in(inj_dummy_in_1755377830763_153),
                .out_val(inj_out_val_1755377830763_115)
            );
            split_for_loop split_for_loop_inst_1755377830637_5270 (
                .start_val_i(inj_in_a_1755377830531_804),
                .sum_out_i(inj_sum_out_i_1755377830637_404),
                .clk_i(clk)
            );
            // BEGIN: case_default_ts1755377830620
            always_comb begin
                inj_out_res_1755377830620_21 = 1'b0;
                case (inj_case_expr_1755377830490_540)
                    2'b01: inj_out_res_1755377830620_21 = 1'b1;
                    2'b10: inj_out_res_1755377830620_21 = 1'b0;
                    default: inj_out_res_1755377830620_21 = 1'b1;
                endcase
            end
            // END: case_default_ts1755377830620

        always_comb begin
            var_m1_ts1755377830614 = in_d;
            inj_out_sum_m1_1755377830614_891 = (++var_m1_ts1755377830614) + inj_in_a_1755377830531_804;
            inj_var_out_m1_1755377830614_259 = var_m1_ts1755377830614;
        end
        // END: expr_preadd_comb_ts1755377830614

        ComplexConversions ComplexConversions_inst_1755377830531_3525 (
            .in_b(in_d),
            .out_concat(inj_out_concat_1755377830531_635),
            .in_a(inj_in_a_1755377830531_804)
        );
        // BEGIN: mod_default_disable_ts1755377830528
        assign inj_out_1755377830528_293 = inj_enable_in_1755377830528_286;
        // END: mod_default_disable_ts1755377830528

    always @(posedge clk) begin
        q1_ts1755377830519 <= inj_a_1755377830492_285;
    end
    always @(q1_ts1755377830519) begin
        q2_ts1755377830519 = ~q1_ts1755377830519;
    end
    assign inj_q_out_1755377830519_395 = q2_ts1755377830519;
    // END: LogicDependencyChain_ts1755377830519

    assign inj_sum_1755377830492_554 = inj_a_1755377830492_285 + inj_b_1755377830492_365;
    // END: simple_adder_ts1755377830492

    always @* begin
        priority casez (inj_case_expr_1755377830490_540)
            2'b1?: inj_internal_out_1755377830490_785 = 5;
            2'b?1: inj_internal_out_1755377830490_785 = 6;  
            2'b0?: inj_internal_out_1755377830490_785 = 7;
            2'b?0: inj_internal_out_1755377830490_785 = 8;  
            default: inj_internal_out_1755377830490_785 = 9;
        endcase
    end
    // END: case_priority_overlapping_mod_ts1755377830490

    CombinationalLogicImplicit CombinationalLogicImplicit_inst_1755377830490_8444 (
        .a(inj_a_1755377830490_312),
        .b(inj_b_1755377830490_364),
        .sum(inj_sum_1755377830490_590)
    );
    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule


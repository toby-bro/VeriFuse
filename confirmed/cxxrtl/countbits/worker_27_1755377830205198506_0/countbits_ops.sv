module BitwiseAssign (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    output logic [3:0] out_y
);
    assign out_y = in_a ^ in_b;
endmodule

module always_multi_stmt_unhandled (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    always_comb begin
        out1 = in1;
        out2 = in2;
    end
endmodule

module ansi_basic (
    input logic clk,
    output logic reset_n
);
    always_comb begin
        reset_n = clk;
    end
endmodule

module member_access_packed_union (
    input logic [31:0] in_val,
    input bit select_a,
    output logic [31:0] out_val
);
    typedef union packed {
        logic [31:0] a; 
        logic [31:0] b; 
    } my_packed_union;
    my_packed_union union_var;
    always_comb begin
        if (select_a)
            union_var.a = in_val;
        else
            union_var.b = in_val[31:0];
        out_val = union_var.a;
    end
endmodule

module mod_name_conflict (
    input logic in_a,
    output logic out_a
);
    logic conflict_var;
    parameter int conflict_param = 1;
    assign out_a = in_a;
endmodule

module simple_undeclared_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input wire [7:0] inj_in_a_1755377830619_624,
    input logic inj_in_a_1755377830739_416,
    input logic [3:0] inj_in_a_1755377830741_970,
    input wire [7:0] inj_in_b_1755377830619_91,
    input logic [3:0] inj_in_b_1755377830741_259,
    input wire [7:0] inj_in_c_1755377830619_518,
    input wire inj_in_cond_neq_lhs_1755377830619_284,
    input wire inj_in_cond_neq_rhs_1755377830619_112,
    input wire inj_in_cond_not_1755377830619_249,
    input wire [7:0] inj_in_not_else_1755377830619_148,
    input wire [7:0] inj_in_not_then_1755377830619_89,
    input logic [31:0] inj_in_val_1755377830600_794,
    input int inj_in_val_1755377830612_330,
    input bit inj_select_a_1755377830600_823,
    input wire rst,
    output logic [3:0] cnt,
    output logic [7:0] inj_out1_1755377830638_51,
    output logic [7:0] inj_out2_1755377830638_704,
    output logic inj_out_a_1755377830739_235,
    output logic inj_out_eq_1755377830619_469,
    output logic inj_out_eq_concat_1755377830619_327,
    output logic inj_out_gt_1755377830619_142,
    output logic inj_out_gte_1755377830619_400,
    output logic inj_out_lt_1755377830619_799,
    output logic inj_out_lte_1755377830619_207,
    output logic inj_out_neq_1755377830619_807,
    output logic inj_out_not_eq_1755377830619_614,
    output logic inj_out_not_neq_1755377830619_41,
    output logic inj_out_ternary_1755377830619_422,
    output logic inj_out_ternary_1bit_0else_1755377830619_72,
    output logic inj_out_ternary_1bit_0then_1755377830619_495,
    output logic inj_out_ternary_1bit_1else_1755377830619_934,
    output logic inj_out_ternary_1bit_1then_1755377830619_922,
    output logic inj_out_ternary_const_cond_false_1755377830619_436,
    output logic inj_out_ternary_const_cond_true_1755377830619_216,
    output logic [7:0] inj_out_ternary_dec_1755377830620_875,
    output logic [7:0] inj_out_ternary_inc_1755377830620_994,
    output logic [7:0] inj_out_ternary_pulled_nots_1755377830620_851,
    output logic inj_out_ternary_swapped_cond_1755377830620_243,
    output logic inj_out_ternary_swapped_neq_cond_1755377830620_891,
    output logic [31:0] inj_out_val_1755377830603_909,
    output int inj_out_val_1755377830612_351,
    output int inj_out_val_1755377831049_224,
    output logic [3:0] inj_out_y_1755377830741_755,
    output logic inj_reset_n_1755377830599_177,
    output logic [3:0] inj_sum_1755377830891_369
);
    // BEGIN: Mod_TernaryLogic_ts1755377830635
    parameter [7:0] CONST_ONE_8 = 8'h01;
    parameter [0:0] CONST_ZERO_1 = 1'b0;
    parameter [0:0] CONST_ONE_1 = 1'b1;
    logic [7:0] intermediate_const_concat_comp_ts1755377830634;
    logic [15:0] intermediate_concat_comp_src_ts1755377830634;
        // BEGIN: definition_used_diag_mod_ts1755377831049
        assign inj_out_val_1755377831049_224 = inj_in_val_1755377830612_330;
        // END: definition_used_diag_mod_ts1755377831049

        // BEGIN: CombinationalLogicImplicit_ts1755377830891
        always @* begin
            inj_sum_1755377830891_369 = inj_in_a_1755377830741_970 + inj_in_b_1755377830741_259;
        end
        // END: CombinationalLogicImplicit_ts1755377830891

        BitwiseAssign BitwiseAssign_inst_1755377830741_1827 (
            .out_y(inj_out_y_1755377830741_755),
            .in_a(inj_in_a_1755377830741_970),
            .in_b(inj_in_b_1755377830741_259)
        );
        mod_name_conflict mod_name_conflict_inst_1755377830739_4024 (
            .in_a(inj_in_a_1755377830739_416),
            .out_a(inj_out_a_1755377830739_235)
        );
        always_multi_stmt_unhandled always_multi_stmt_unhandled_inst_1755377830638_7020 (
            .out2(inj_out2_1755377830638_704),
            .in1(in_d),
            .in2(intermediate_const_concat_comp_ts1755377830634),
            .out1(inj_out1_1755377830638_51)
        );
    always_comb begin
        inj_out_eq_1755377830619_469 = (inj_in_a_1755377830619_624 == inj_in_b_1755377830619_91);
        inj_out_neq_1755377830619_807 = (inj_in_a_1755377830619_624 != inj_in_b_1755377830619_91);
        inj_out_gt_1755377830619_142 = (inj_in_a_1755377830619_624 > inj_in_b_1755377830619_91);
        inj_out_lt_1755377830619_799 = (inj_in_a_1755377830619_624 < inj_in_b_1755377830619_91);
        inj_out_gte_1755377830619_400 = (inj_in_a_1755377830619_624 >= inj_in_b_1755377830619_91);
        inj_out_lte_1755377830619_207 = (inj_in_a_1755377830619_624 <= inj_in_b_1755377830619_91);
        inj_out_not_eq_1755377830619_614 = !(inj_in_a_1755377830619_624 == inj_in_b_1755377830619_91);
        inj_out_not_neq_1755377830619_41 = !(inj_in_a_1755377830619_624 != inj_in_b_1755377830619_91);
        intermediate_const_concat_comp_ts1755377830634 = 8'hAA;
        intermediate_concat_comp_src_ts1755377830634 = {inj_in_a_1755377830619_624, inj_in_b_1755377830619_91};
        inj_out_eq_concat_1755377830619_327 = (intermediate_const_concat_comp_ts1755377830634 == intermediate_concat_comp_src_ts1755377830634[7:0]);
        inj_out_ternary_1755377830619_422 = rst ? inj_in_a_1755377830619_624[0] : inj_in_b_1755377830619_91[0];
        inj_out_ternary_const_cond_true_1755377830619_216 = 1'b1 ? inj_in_a_1755377830619_624[0] : inj_in_b_1755377830619_91[0];
        inj_out_ternary_const_cond_false_1755377830619_436 = 1'b0 ? inj_in_a_1755377830619_624[0] : inj_in_b_1755377830619_91[0];
        inj_out_ternary_swapped_cond_1755377830620_243 = !inj_in_cond_not_1755377830619_249 ? inj_in_a_1755377830619_624[0] : inj_in_b_1755377830619_91[0];
        inj_out_ternary_swapped_neq_cond_1755377830620_891 = (inj_in_cond_neq_lhs_1755377830619_284 != inj_in_cond_neq_rhs_1755377830619_112) ? inj_in_a_1755377830619_624[0] : inj_in_b_1755377830619_91[0];
        inj_out_ternary_pulled_nots_1755377830620_851 = rst ? ~inj_in_not_then_1755377830619_89 : ~inj_in_not_else_1755377830619_148;
        inj_out_ternary_inc_1755377830620_994 = rst ? (inj_in_a_1755377830619_624 + CONST_ONE_8) : inj_in_a_1755377830619_624;
        inj_out_ternary_dec_1755377830620_875 = rst ? (inj_in_a_1755377830619_624 - CONST_ONE_8) : inj_in_a_1755377830619_624;
        inj_out_ternary_1bit_0then_1755377830619_495 = rst ? CONST_ZERO_1 : clk;
        inj_out_ternary_1bit_1then_1755377830619_922 = rst ? CONST_ONE_1 : clk;
        inj_out_ternary_1bit_0else_1755377830619_72 = rst ? clk : CONST_ZERO_1;
        inj_out_ternary_1bit_1else_1755377830619_934 = rst ? clk : CONST_ONE_1;
    end
    // END: Mod_TernaryLogic_ts1755377830635

    simple_undeclared_mod simple_undeclared_mod_inst_1755377830612_4898 (
        .in_val(inj_in_val_1755377830612_330),
        .out_val(inj_out_val_1755377830612_351)
    );
    member_access_packed_union member_access_packed_union_inst_1755377830603_6965 (
        .in_val(inj_in_val_1755377830600_794),
        .select_a(inj_select_a_1755377830600_823),
        .out_val(inj_out_val_1755377830603_909)
    );
    ansi_basic ansi_basic_inst_1755377830599_7939 (
        .clk(clk),
        .reset_n(inj_reset_n_1755377830599_177)
    );
    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule


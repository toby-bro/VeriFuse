module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module multi_always_comb (
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [7:0] out1,
    output wire [7:0] out2
);
    logic [7:0] intermediate1;
    logic [7:0] intermediate2;
    always @(*) begin
        intermediate1 = in1 & in2;
    end
    always @(*) begin
        intermediate2 = in1 | in2;
    end
    assign out1 = intermediate1 + 8'd1;
    assign out2 = intermediate2 - 8'd1;
endmodule

module remaining_reduction_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic nand_out,
    output logic nor_out,
    output logic xnor_out
);
    assign nand_out = ~&in1;
    assign nor_out = ~|in2;
    assign xnor_out = ^~in3;
endmodule

module unsupported_cond_expr (
    input bit condition_m10,
    input logic [7:0] in_val_m10,
    output logic [7:0] out_val_m10
);
    logic [7:0] var_m10;
    always_comb begin
        var_m10 = in_val_m10;
        out_val_m10 = condition_m10 ? var_m10 : var_m10;
        var_m10++;
    end
endmodule

module m_caseeq_demo (
    input wire clk,
    input logic in,
    input bit inj_condition_m10_1755351743672_470,
    input logic [9:0] inj_data_in_pl_1755351743721_249,
    input wire [15:0] inj_dcac_start_val_1755351743527_742,
    input wire [7:0] inj_in1_1755351743486_683,
    input logic [7:0] inj_in1_1755351743714_553,
    input wire [7:0] inj_in2_1755351743486_583,
    input logic [7:0] inj_in3_1755351743714_88,
    input logic [7:0] inj_in_val_m10_1755351743672_115,
    input int inj_val_false_1755351743831_806,
    input int inj_val_true_1755351743831_159,
    input wire rst,
    output logic eq,
    output bit inj_d_out_1755351743739_966,
    output logic [4:0] inj_data_out_pl_1755351743721_740,
    output logic [15:0] inj_dcac_end_val_1755351743527_10,
    output logic inj_nand_out_1755351743714_339,
    output logic inj_nor_out_1755351743714_351,
    output wire [7:0] inj_out1_1755351743486_508,
    output wire [7:0] inj_out2_1755351743486_898,
    output int inj_out_val_1755351743831_180,
    output logic [7:0] inj_out_val_m10_1755351743672_256,
    output logic inj_xnor_out_1755351743714_231,
    output logic neq
);
    logic tri_sig = 1'bz;
    // BEGIN: deep_comb_assign_chain_ts1755351743583
    logic [15:0] t1_ts1755351743527, t2_ts1755351743527, t3_ts1755351743527, t4_ts1755351743527, t5_ts1755351743527, t6_ts1755351743527, t7_ts1755351743527, t8_ts1755351743527, t9_ts1755351743527, t10_ts1755351743527;
    logic [15:0] t11_ts1755351743527, t12_ts1755351743527, t13_ts1755351743527, t14_ts1755351743527, t15_ts1755351743527, t16_ts1755351743527, t17_ts1755351743527, t18_ts1755351743527, t19_ts1755351743527, t20_ts1755351743527;
    logic [15:0] t21_ts1755351743527, t22_ts1755351743527, t23_ts1755351743527, t24_ts1755351743527, t25_ts1755351743527, t26_ts1755351743527, t27_ts1755351743527, t28_ts1755351743527, t29_ts1755351743527, t30_ts1755351743527;
    logic [15:0] t31_ts1755351743527, t32_ts1755351743527, t33_ts1755351743527, t34_ts1755351743527, t35_ts1755351743527, t36_ts1755351743527, t37_ts1755351743527, t38_ts1755351743527, t39_ts1755351743527, t40_ts1755351743527;
        // BEGIN: module_packed_logic_ts1755351743721
        logic [15:0] my_packed_logic_ts1755351743721 ;
            // BEGIN: ConditionalOps_ts1755351743831
            assign inj_out_val_1755351743831_180 = in ? inj_val_true_1755351743831_159 : inj_val_false_1755351743831_806;
            // END: ConditionalOps_ts1755351743831

            // BEGIN: DummyBindTarget_ts1755351743739
            assign inj_d_out_1755351743739_966 = inj_condition_m10_1755351743672_470;
            BindSimpleModule u_bind (.in(inj_condition_m10_1755351743672_470), .out());
            // END: DummyBindTarget_ts1755351743739

        always_comb begin
            my_packed_logic_ts1755351743721[9:0] = inj_data_in_pl_1755351743721_249;
            my_packed_logic_ts1755351743721[15:10] = 6'h3F;
            my_packed_logic_ts1755351743721[0] = in;
        end
        assign inj_data_out_pl_1755351743721_740[4:1] = my_packed_logic_ts1755351743721[4:1];
        assign inj_data_out_pl_1755351743721_740[0] = my_packed_logic_ts1755351743721[1];
        // END: module_packed_logic_ts1755351743721

        remaining_reduction_ops remaining_reduction_ops_inst_1755351743714_5811 (
            .in2(inj_in_val_m10_1755351743672_115),
            .in3(inj_in3_1755351743714_88),
            .nand_out(inj_nand_out_1755351743714_339),
            .nor_out(inj_nor_out_1755351743714_351),
            .xnor_out(inj_xnor_out_1755351743714_231),
            .in1(inj_in1_1755351743714_553)
        );
        unsupported_cond_expr unsupported_cond_expr_inst_1755351743672_127 (
            .condition_m10(inj_condition_m10_1755351743672_470),
            .in_val_m10(inj_in_val_m10_1755351743672_115),
            .out_val_m10(inj_out_val_m10_1755351743672_256)
        );
    always_comb begin
        t1_ts1755351743527 = inj_dcac_start_val_1755351743527_742 + 1;
        t2_ts1755351743527 = t1_ts1755351743527 * 2;
        t3_ts1755351743527 = t2_ts1755351743527 - 3;
        t4_ts1755351743527 = t3_ts1755351743527 ^ 4;
        t5_ts1755351743527 = t4_ts1755351743527 | 5;
        t6_ts1755351743527 = t5_ts1755351743527 & 6;
        t7_ts1755351743527 = t6_ts1755351743527 + 7;
        t8_ts1755351743527 = t7_ts1755351743527 - 8;
        t9_ts1755351743527 = t8_ts1755351743527 ^ 9;
        t10_ts1755351743527 = t9_ts1755351743527 | 10;
        t11_ts1755351743527 = t10_ts1755351743527 & 11;
        t12_ts1755351743527 = t11_ts1755351743527 + 12;
        t13_ts1755351743527 = t12_ts1755351743527 - 13;
        t14_ts1755351743527 = t13_ts1755351743527 ^ 14;
        t15_ts1755351743527 = t14_ts1755351743527 | 15;
        t16_ts1755351743527 = t15_ts1755351743527 + 16;
        t17_ts1755351743527 = t16_ts1755351743527 * 17;
        t18_ts1755351743527 = t17_ts1755351743527 - 18;
        t19_ts1755351743527 = t18_ts1755351743527 ^ 19;
        t20_ts1755351743527 = t19_ts1755351743527 | 20;
        t21_ts1755351743527 = t20_ts1755351743527 + 1;
        t22_ts1755351743527 = t21_ts1755351743527 * 2;
        t23_ts1755351743527 = t22_ts1755351743527 - 3;
        t24_ts1755351743527 = t23_ts1755351743527 ^ 4;
        t25_ts1755351743527 = t24_ts1755351743527 | 5;
        t26_ts1755351743527 = t25_ts1755351743527 & 6;
        t27_ts1755351743527 = t26_ts1755351743527 + 7;
        t28_ts1755351743527 = t27_ts1755351743527 - 8;
        t29_ts1755351743527 = t28_ts1755351743527 ^ 9;
        t30_ts1755351743527 = t29_ts1755351743527 | 10;
        t31_ts1755351743527 = t30_ts1755351743527 & 11;
        t32_ts1755351743527 = t31_ts1755351743527 + 12;
        t33_ts1755351743527 = t32_ts1755351743527 - 13;
        t34_ts1755351743527 = t33_ts1755351743527 ^ 14;
        t35_ts1755351743527 = t34_ts1755351743527 | 15;
        t36_ts1755351743527 = t35_ts1755351743527 + 16;
        t37_ts1755351743527 = t36_ts1755351743527 * 17;
        t38_ts1755351743527 = t37_ts1755351743527 - 18;
        t39_ts1755351743527 = t38_ts1755351743527 ^ 19;
        t40_ts1755351743527 = t39_ts1755351743527 | 20;
        inj_dcac_end_val_1755351743527_10 = t40_ts1755351743527;
    end
    // END: deep_comb_assign_chain_ts1755351743583

    multi_always_comb multi_always_comb_inst_1755351743486_2125 (
        .in1(inj_in1_1755351743486_683),
        .in2(inj_in2_1755351743486_583),
        .out1(inj_out1_1755351743486_508),
        .out2(inj_out2_1755351743486_898)
    );
    assign eq  = (in === tri_sig); 
    assign neq = (in !== tri_sig); 
endmodule


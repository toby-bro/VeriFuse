module BindSimpleModule (
	in,
	out
);
	input wire in;
	output wire out;
	assign out = in;
endmodule
module multi_always_comb (
	in1,
	in2,
	out1,
	out2
);
	input wire [7:0] in1;
	input wire [7:0] in2;
	output wire [7:0] out1;
	output wire [7:0] out2;
	reg [7:0] intermediate1;
	reg [7:0] intermediate2;
	always @(*) intermediate1 = in1 & in2;
	always @(*) intermediate2 = in1 | in2;
	assign out1 = intermediate1 + 8'd1;
	assign out2 = intermediate2 - 8'd1;
endmodule
module remaining_reduction_ops (
	in1,
	in2,
	in3,
	nand_out,
	nor_out,
	xnor_out
);
	input wire [7:0] in1;
	input wire [7:0] in2;
	input wire [7:0] in3;
	output wire nand_out;
	output wire nor_out;
	output wire xnor_out;
	assign nand_out = ~&in1;
	assign nor_out = ~|in2;
	assign xnor_out = ~^in3;
endmodule
module unsupported_cond_expr (
	condition_m10,
	in_val_m10,
	out_val_m10
);
	reg _sv2v_0;
	input wire condition_m10;
	input wire [7:0] in_val_m10;
	output reg [7:0] out_val_m10;
	reg [7:0] var_m10;
	always @(*) begin
		if (_sv2v_0)
			;
		var_m10 = in_val_m10;
		out_val_m10 = (condition_m10 ? var_m10 : var_m10);
		var_m10 = var_m10 + 1;
	end
	initial _sv2v_0 = 0;
endmodule
module m_caseeq_demo (
	clk,
	in,
	inj_condition_m10_1755351743672_470,
	inj_data_in_pl_1755351743721_249,
	inj_dcac_start_val_1755351743527_742,
	inj_in1_1755351743486_683,
	inj_in1_1755351743714_553,
	inj_in2_1755351743486_583,
	inj_in3_1755351743714_88,
	inj_in_val_m10_1755351743672_115,
	inj_val_false_1755351743831_806,
	inj_val_true_1755351743831_159,
	rst,
	eq,
	inj_d_out_1755351743739_966,
	inj_data_out_pl_1755351743721_740,
	inj_dcac_end_val_1755351743527_10,
	inj_nand_out_1755351743714_339,
	inj_nor_out_1755351743714_351,
	inj_out1_1755351743486_508,
	inj_out2_1755351743486_898,
	inj_out_val_1755351743831_180,
	inj_out_val_m10_1755351743672_256,
	inj_xnor_out_1755351743714_231,
	neq
);
	reg _sv2v_0;
	input wire clk;
	input wire in;
	input wire inj_condition_m10_1755351743672_470;
	input wire [9:0] inj_data_in_pl_1755351743721_249;
	input wire [15:0] inj_dcac_start_val_1755351743527_742;
	input wire [7:0] inj_in1_1755351743486_683;
	input wire [7:0] inj_in1_1755351743714_553;
	input wire [7:0] inj_in2_1755351743486_583;
	input wire [7:0] inj_in3_1755351743714_88;
	input wire [7:0] inj_in_val_m10_1755351743672_115;
	input wire signed [31:0] inj_val_false_1755351743831_806;
	input wire signed [31:0] inj_val_true_1755351743831_159;
	input wire rst;
	output wire eq;
	output wire inj_d_out_1755351743739_966;
	output wire [4:0] inj_data_out_pl_1755351743721_740;
	output reg [15:0] inj_dcac_end_val_1755351743527_10;
	output wire inj_nand_out_1755351743714_339;
	output wire inj_nor_out_1755351743714_351;
	output wire [7:0] inj_out1_1755351743486_508;
	output wire [7:0] inj_out2_1755351743486_898;
	output wire signed [31:0] inj_out_val_1755351743831_180;
	output wire [7:0] inj_out_val_m10_1755351743672_256;
	output wire inj_xnor_out_1755351743714_231;
	output wire neq;
	reg tri_sig = 1'bz;
	reg [15:0] t1_ts1755351743527;
	reg [15:0] t2_ts1755351743527;
	reg [15:0] t3_ts1755351743527;
	reg [15:0] t4_ts1755351743527;
	reg [15:0] t5_ts1755351743527;
	reg [15:0] t6_ts1755351743527;
	reg [15:0] t7_ts1755351743527;
	reg [15:0] t8_ts1755351743527;
	reg [15:0] t9_ts1755351743527;
	reg [15:0] t10_ts1755351743527;
	reg [15:0] t11_ts1755351743527;
	reg [15:0] t12_ts1755351743527;
	reg [15:0] t13_ts1755351743527;
	reg [15:0] t14_ts1755351743527;
	reg [15:0] t15_ts1755351743527;
	reg [15:0] t16_ts1755351743527;
	reg [15:0] t17_ts1755351743527;
	reg [15:0] t18_ts1755351743527;
	reg [15:0] t19_ts1755351743527;
	reg [15:0] t20_ts1755351743527;
	reg [15:0] t21_ts1755351743527;
	reg [15:0] t22_ts1755351743527;
	reg [15:0] t23_ts1755351743527;
	reg [15:0] t24_ts1755351743527;
	reg [15:0] t25_ts1755351743527;
	reg [15:0] t26_ts1755351743527;
	reg [15:0] t27_ts1755351743527;
	reg [15:0] t28_ts1755351743527;
	reg [15:0] t29_ts1755351743527;
	reg [15:0] t30_ts1755351743527;
	reg [15:0] t31_ts1755351743527;
	reg [15:0] t32_ts1755351743527;
	reg [15:0] t33_ts1755351743527;
	reg [15:0] t34_ts1755351743527;
	reg [15:0] t35_ts1755351743527;
	reg [15:0] t36_ts1755351743527;
	reg [15:0] t37_ts1755351743527;
	reg [15:0] t38_ts1755351743527;
	reg [15:0] t39_ts1755351743527;
	reg [15:0] t40_ts1755351743527;
	reg [15:0] my_packed_logic_ts1755351743721;
	assign inj_out_val_1755351743831_180 = (in ? inj_val_true_1755351743831_159 : inj_val_false_1755351743831_806);
	assign inj_d_out_1755351743739_966 = inj_condition_m10_1755351743672_470;
	BindSimpleModule u_bind(
		.in(inj_condition_m10_1755351743672_470),
		.out()
	);
	always @(*) begin
		if (_sv2v_0)
			;
		my_packed_logic_ts1755351743721[9:0] = inj_data_in_pl_1755351743721_249;
		my_packed_logic_ts1755351743721[15:10] = 6'h3f;
		my_packed_logic_ts1755351743721[0] = in;
	end
	assign inj_data_out_pl_1755351743721_740[4:1] = my_packed_logic_ts1755351743721[4:1];
	assign inj_data_out_pl_1755351743721_740[0] = my_packed_logic_ts1755351743721[1];
	remaining_reduction_ops remaining_reduction_ops_inst_1755351743714_5811(
		.in2(inj_in_val_m10_1755351743672_115),
		.in3(inj_in3_1755351743714_88),
		.nand_out(inj_nand_out_1755351743714_339),
		.nor_out(inj_nor_out_1755351743714_351),
		.xnor_out(inj_xnor_out_1755351743714_231),
		.in1(inj_in1_1755351743714_553)
	);
	unsupported_cond_expr unsupported_cond_expr_inst_1755351743672_127(
		.condition_m10(inj_condition_m10_1755351743672_470),
		.in_val_m10(inj_in_val_m10_1755351743672_115),
		.out_val_m10(inj_out_val_m10_1755351743672_256)
	);
	always @(*) begin
		if (_sv2v_0)
			;
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
	multi_always_comb multi_always_comb_inst_1755351743486_2125(
		.in1(inj_in1_1755351743486_683),
		.in2(inj_in2_1755351743486_583),
		.out1(inj_out1_1755351743486_508),
		.out2(inj_out2_1755351743486_898)
	);
	assign eq = in === tri_sig;
	assign neq = in !== tri_sig;
	initial _sv2v_0 = 0;
endmodule
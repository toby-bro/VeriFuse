module BitwiseAssign (
	in_a,
	in_b,
	out_y
);
	input wire [3:0] in_a;
	input wire [3:0] in_b;
	output wire [3:0] out_y;
	assign out_y = in_a ^ in_b;
endmodule
module always_multi_stmt_unhandled (
	in1,
	in2,
	out1,
	out2
);
	reg _sv2v_0;
	input wire [7:0] in1;
	input wire [7:0] in2;
	output reg [7:0] out1;
	output reg [7:0] out2;
	always @(*) begin
		if (_sv2v_0)
			;
		out1 = in1;
		out2 = in2;
	end
	initial _sv2v_0 = 0;
endmodule
module ansi_basic (
	clk,
	reset_n
);
	reg _sv2v_0;
	input wire clk;
	output reg reset_n;
	always @(*) begin
		if (_sv2v_0)
			;
		reset_n = clk;
	end
	initial _sv2v_0 = 0;
endmodule
module member_access_packed_union (
	in_val,
	select_a,
	out_val
);
	reg _sv2v_0;
	input wire [31:0] in_val;
	input wire select_a;
	output reg [31:0] out_val;
	reg [31:0] union_var;
	always @(*) begin
		if (_sv2v_0)
			;
		if (select_a)
			union_var[31-:32] = in_val;
		else
			union_var[31-:32] = in_val[31:0];
		out_val = union_var[31-:32];
	end
	initial _sv2v_0 = 0;
endmodule
module mod_name_conflict (
	in_a,
	out_a
);
	input wire in_a;
	output wire out_a;
	wire conflict_var;
	parameter signed [31:0] conflict_param = 1;
	assign out_a = in_a;
endmodule
module simple_undeclared_mod (
	in_val,
	out_val
);
	input wire signed [31:0] in_val;
	output wire signed [31:0] out_val;
	assign out_val = in_val;
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_in_a_1755377830619_624,
	inj_in_a_1755377830739_416,
	inj_in_a_1755377830741_970,
	inj_in_b_1755377830619_91,
	inj_in_b_1755377830741_259,
	inj_in_c_1755377830619_518,
	inj_in_cond_neq_lhs_1755377830619_284,
	inj_in_cond_neq_rhs_1755377830619_112,
	inj_in_cond_not_1755377830619_249,
	inj_in_not_else_1755377830619_148,
	inj_in_not_then_1755377830619_89,
	inj_in_val_1755377830600_794,
	inj_in_val_1755377830612_330,
	inj_select_a_1755377830600_823,
	rst,
	cnt,
	inj_out1_1755377830638_51,
	inj_out2_1755377830638_704,
	inj_out_a_1755377830739_235,
	inj_out_eq_1755377830619_469,
	inj_out_eq_concat_1755377830619_327,
	inj_out_gt_1755377830619_142,
	inj_out_gte_1755377830619_400,
	inj_out_lt_1755377830619_799,
	inj_out_lte_1755377830619_207,
	inj_out_neq_1755377830619_807,
	inj_out_not_eq_1755377830619_614,
	inj_out_not_neq_1755377830619_41,
	inj_out_ternary_1755377830619_422,
	inj_out_ternary_1bit_0else_1755377830619_72,
	inj_out_ternary_1bit_0then_1755377830619_495,
	inj_out_ternary_1bit_1else_1755377830619_934,
	inj_out_ternary_1bit_1then_1755377830619_922,
	inj_out_ternary_const_cond_false_1755377830619_436,
	inj_out_ternary_const_cond_true_1755377830619_216,
	inj_out_ternary_dec_1755377830620_875,
	inj_out_ternary_inc_1755377830620_994,
	inj_out_ternary_pulled_nots_1755377830620_851,
	inj_out_ternary_swapped_cond_1755377830620_243,
	inj_out_ternary_swapped_neq_cond_1755377830620_891,
	inj_out_val_1755377830603_909,
	inj_out_val_1755377830612_351,
	inj_out_val_1755377831049_224,
	inj_out_y_1755377830741_755,
	inj_reset_n_1755377830599_177,
	inj_sum_1755377830891_369
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] in_d;
	input wire [7:0] inj_in_a_1755377830619_624;
	input wire inj_in_a_1755377830739_416;
	input wire [3:0] inj_in_a_1755377830741_970;
	input wire [7:0] inj_in_b_1755377830619_91;
	input wire [3:0] inj_in_b_1755377830741_259;
	input wire [7:0] inj_in_c_1755377830619_518;
	input wire inj_in_cond_neq_lhs_1755377830619_284;
	input wire inj_in_cond_neq_rhs_1755377830619_112;
	input wire inj_in_cond_not_1755377830619_249;
	input wire [7:0] inj_in_not_else_1755377830619_148;
	input wire [7:0] inj_in_not_then_1755377830619_89;
	input wire [31:0] inj_in_val_1755377830600_794;
	input wire signed [31:0] inj_in_val_1755377830612_330;
	input wire inj_select_a_1755377830600_823;
	input wire rst;
	output wire [3:0] cnt;
	output wire [7:0] inj_out1_1755377830638_51;
	output wire [7:0] inj_out2_1755377830638_704;
	output wire inj_out_a_1755377830739_235;
	output reg inj_out_eq_1755377830619_469;
	output reg inj_out_eq_concat_1755377830619_327;
	output reg inj_out_gt_1755377830619_142;
	output reg inj_out_gte_1755377830619_400;
	output reg inj_out_lt_1755377830619_799;
	output reg inj_out_lte_1755377830619_207;
	output reg inj_out_neq_1755377830619_807;
	output reg inj_out_not_eq_1755377830619_614;
	output reg inj_out_not_neq_1755377830619_41;
	output reg inj_out_ternary_1755377830619_422;
	output reg inj_out_ternary_1bit_0else_1755377830619_72;
	output reg inj_out_ternary_1bit_0then_1755377830619_495;
	output reg inj_out_ternary_1bit_1else_1755377830619_934;
	output reg inj_out_ternary_1bit_1then_1755377830619_922;
	output reg inj_out_ternary_const_cond_false_1755377830619_436;
	output reg inj_out_ternary_const_cond_true_1755377830619_216;
	output reg [7:0] inj_out_ternary_dec_1755377830620_875;
	output reg [7:0] inj_out_ternary_inc_1755377830620_994;
	output reg [7:0] inj_out_ternary_pulled_nots_1755377830620_851;
	output reg inj_out_ternary_swapped_cond_1755377830620_243;
	output reg inj_out_ternary_swapped_neq_cond_1755377830620_891;
	output wire [31:0] inj_out_val_1755377830603_909;
	output wire signed [31:0] inj_out_val_1755377830612_351;
	output wire signed [31:0] inj_out_val_1755377831049_224;
	output wire [3:0] inj_out_y_1755377830741_755;
	output wire inj_reset_n_1755377830599_177;
	output reg [3:0] inj_sum_1755377830891_369;
	parameter [7:0] CONST_ONE_8 = 8'h01;
	parameter [0:0] CONST_ZERO_1 = 1'b0;
	parameter [0:0] CONST_ONE_1 = 1'b1;
	reg [7:0] intermediate_const_concat_comp_ts1755377830634;
	reg [15:0] intermediate_concat_comp_src_ts1755377830634;
	assign inj_out_val_1755377831049_224 = inj_in_val_1755377830612_330;
	always @(*) inj_sum_1755377830891_369 = inj_in_a_1755377830741_970 + inj_in_b_1755377830741_259;
	BitwiseAssign BitwiseAssign_inst_1755377830741_1827(
		.out_y(inj_out_y_1755377830741_755),
		.in_a(inj_in_a_1755377830741_970),
		.in_b(inj_in_b_1755377830741_259)
	);
	mod_name_conflict mod_name_conflict_inst_1755377830739_4024(
		.in_a(inj_in_a_1755377830739_416),
		.out_a(inj_out_a_1755377830739_235)
	);
	always_multi_stmt_unhandled always_multi_stmt_unhandled_inst_1755377830638_7020(
		.out2(inj_out2_1755377830638_704),
		.in1(in_d),
		.in2(intermediate_const_concat_comp_ts1755377830634),
		.out1(inj_out1_1755377830638_51)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		inj_out_eq_1755377830619_469 = inj_in_a_1755377830619_624 == inj_in_b_1755377830619_91;
		inj_out_neq_1755377830619_807 = inj_in_a_1755377830619_624 != inj_in_b_1755377830619_91;
		inj_out_gt_1755377830619_142 = inj_in_a_1755377830619_624 > inj_in_b_1755377830619_91;
		inj_out_lt_1755377830619_799 = inj_in_a_1755377830619_624 < inj_in_b_1755377830619_91;
		inj_out_gte_1755377830619_400 = inj_in_a_1755377830619_624 >= inj_in_b_1755377830619_91;
		inj_out_lte_1755377830619_207 = inj_in_a_1755377830619_624 <= inj_in_b_1755377830619_91;
		inj_out_not_eq_1755377830619_614 = inj_in_a_1755377830619_624 != inj_in_b_1755377830619_91;
		inj_out_not_neq_1755377830619_41 = inj_in_a_1755377830619_624 == inj_in_b_1755377830619_91;
		intermediate_const_concat_comp_ts1755377830634 = 8'haa;
		intermediate_concat_comp_src_ts1755377830634 = {inj_in_a_1755377830619_624, inj_in_b_1755377830619_91};
		inj_out_eq_concat_1755377830619_327 = intermediate_const_concat_comp_ts1755377830634 == intermediate_concat_comp_src_ts1755377830634[7:0];
		inj_out_ternary_1755377830619_422 = (rst ? inj_in_a_1755377830619_624[0] : inj_in_b_1755377830619_91[0]);
		inj_out_ternary_const_cond_true_1755377830619_216 = inj_in_a_1755377830619_624[0];
		inj_out_ternary_const_cond_false_1755377830619_436 = inj_in_b_1755377830619_91[0];
		inj_out_ternary_swapped_cond_1755377830620_243 = (!inj_in_cond_not_1755377830619_249 ? inj_in_a_1755377830619_624[0] : inj_in_b_1755377830619_91[0]);
		inj_out_ternary_swapped_neq_cond_1755377830620_891 = (inj_in_cond_neq_lhs_1755377830619_284 != inj_in_cond_neq_rhs_1755377830619_112 ? inj_in_a_1755377830619_624[0] : inj_in_b_1755377830619_91[0]);
		inj_out_ternary_pulled_nots_1755377830620_851 = (rst ? ~inj_in_not_then_1755377830619_89 : ~inj_in_not_else_1755377830619_148);
		inj_out_ternary_inc_1755377830620_994 = (rst ? inj_in_a_1755377830619_624 + CONST_ONE_8 : inj_in_a_1755377830619_624);
		inj_out_ternary_dec_1755377830620_875 = (rst ? inj_in_a_1755377830619_624 - CONST_ONE_8 : inj_in_a_1755377830619_624);
		inj_out_ternary_1bit_0then_1755377830619_495 = (rst ? CONST_ZERO_1 : clk);
		inj_out_ternary_1bit_1then_1755377830619_922 = (rst ? CONST_ONE_1 : clk);
		inj_out_ternary_1bit_0else_1755377830619_72 = (rst ? clk : CONST_ZERO_1);
		inj_out_ternary_1bit_1else_1755377830619_934 = (rst ? clk : CONST_ONE_1);
	end
	simple_undeclared_mod simple_undeclared_mod_inst_1755377830612_4898(
		.in_val(inj_in_val_1755377830612_330),
		.out_val(inj_out_val_1755377830612_351)
	);
	member_access_packed_union member_access_packed_union_inst_1755377830603_6965(
		.in_val(inj_in_val_1755377830600_794),
		.select_a(inj_select_a_1755377830600_823),
		.out_val(inj_out_val_1755377830603_909)
	);
	ansi_basic ansi_basic_inst_1755377830599_7939(
		.clk(clk),
		.reset_n(inj_reset_n_1755377830599_177)
	);
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
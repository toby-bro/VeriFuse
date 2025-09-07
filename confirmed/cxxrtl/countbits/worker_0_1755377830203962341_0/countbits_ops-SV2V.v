module CombinationalLogicImplicit (
	a,
	b,
	sum
);
	input wire [3:0] a;
	input wire [3:0] b;
	output reg [3:0] sum;
	always @(*) sum = a + b;
endmodule
module ComplexConversions (
	in_a,
	in_b,
	out_concat
);
	reg _sv2v_0;
	input wire [7:0] in_a;
	input wire [7:0] in_b;
	output reg [15:0] out_concat;
	always @(*) begin
		if (_sv2v_0)
			;
		out_concat = {in_a, in_b};
	end
	initial _sv2v_0 = 0;
endmodule
module ModuleBasic (
	a,
	b,
	out_a,
	out_b
);
	reg _sv2v_0;
	input wire a;
	input wire signed [31:0] b;
	output wire out_a;
	output wire signed [31:0] out_b;
	parameter signed [31:0] P1 = 10;
	localparam signed [31:0] LP1 = 20;
	reg c;
	wire signed [31:0] d;
	always @(*) begin : sv2v_autoblock_1
		reg temp_v;
		if (_sv2v_0)
			;
		temp_v = d;
		c = temp_v;
	end
	assign out_a = a;
	assign d = b;
	assign out_b = (d + P1) + LP1;
	initial _sv2v_0 = 0;
endmodule
module recursive_param_diag_mod (
	dummy_in,
	out_val
);
	input wire signed [31:0] dummy_in;
	output wire signed [31:0] out_val;
	assign out_val = dummy_in;
endmodule
module sequential_always_assign (
	clk,
	in,
	out
);
	input wire clk;
	input wire [7:0] in;
	output reg [7:0] out;
	always @(posedge clk) out <= in;
endmodule
module split_for_loop (
	clk_i,
	start_val_i,
	sum_out_i
);
	input wire clk_i;
	input wire [7:0] start_val_i;
	output reg [15:0] sum_out_i;
	always @(posedge clk_i) begin
		sum_out_i <= 0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < 4; i = i + 1)
				sum_out_i <= (sum_out_i + start_val_i) + i;
		end
	end
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_a_1755377830490_312,
	inj_a_1755377830492_285,
	inj_b_1755377830490_364,
	inj_b_1755377830492_365,
	inj_case_expr_1755377830490_540,
	inj_dummy_in_1755377830763_153,
	inj_enable_in_1755377830528_286,
	inj_in_a_1755377830531_804,
	rst,
	cnt,
	inj_internal_out_1755377830490_785,
	inj_internal_out_1755377831049_504,
	inj_out_1755377830528_293,
	inj_out_1755377831208_1,
	inj_out_a_1755377830867_226,
	inj_out_b_1755377830867_326,
	inj_out_concat_1755377830531_635,
	inj_out_res_1755377830620_21,
	inj_out_sum_m1_1755377830614_891,
	inj_out_val_1755377830763_115,
	inj_q_out_1755377830519_395,
	inj_sum_1755377830490_590,
	inj_sum_1755377830492_554,
	inj_sum_out_i_1755377830637_404,
	inj_var_out_m1_1755377830614_259
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] in_d;
	input wire [3:0] inj_a_1755377830490_312;
	input wire inj_a_1755377830492_285;
	input wire [3:0] inj_b_1755377830490_364;
	input wire inj_b_1755377830492_365;
	input wire [1:0] inj_case_expr_1755377830490_540;
	input wire signed [31:0] inj_dummy_in_1755377830763_153;
	input wire inj_enable_in_1755377830528_286;
	input wire [7:0] inj_in_a_1755377830531_804;
	input wire rst;
	output wire [3:0] cnt;
	output reg [4:0] inj_internal_out_1755377830490_785;
	output reg [4:0] inj_internal_out_1755377831049_504;
	output wire inj_out_1755377830528_293;
	output wire [7:0] inj_out_1755377831208_1;
	output wire inj_out_a_1755377830867_226;
	output wire signed [31:0] inj_out_b_1755377830867_326;
	output wire [15:0] inj_out_concat_1755377830531_635;
	output reg inj_out_res_1755377830620_21;
	output reg [7:0] inj_out_sum_m1_1755377830614_891;
	output wire signed [31:0] inj_out_val_1755377830763_115;
	output wire inj_q_out_1755377830519_395;
	output wire [3:0] inj_sum_1755377830490_590;
	output wire inj_sum_1755377830492_554;
	output wire [15:0] inj_sum_out_i_1755377830637_404;
	output reg [7:0] inj_var_out_m1_1755377830614_259;
	reg q1_ts1755377830519;
	reg q2_ts1755377830519;
	reg [7:0] var_m1_ts1755377830614;
	sequential_always_assign sequential_always_assign_inst_1755377831208_2049(
		.in(var_m1_ts1755377830614),
		.out(inj_out_1755377831208_1),
		.clk(clk)
	);
	always @(*)
		(* full_case, parallel_case *)
		casez ({inj_case_expr_1755377830490_540[0], inj_a_1755377830490_312[3:2], inj_case_expr_1755377830490_540[1]})
			4'b1z0z: inj_internal_out_1755377831049_504 = 30;
			4'bz101: inj_internal_out_1755377831049_504 = 31;
			4'b0z1z: inj_internal_out_1755377831049_504 = 32;
			4'b1z1z: inj_internal_out_1755377831049_504 = 33;
			4'bz111: inj_internal_out_1755377831049_504 = 34;
		endcase
	ModuleBasic ModuleBasic_inst_1755377830867_5062(
		.a(q1_ts1755377830519),
		.b(inj_dummy_in_1755377830763_153),
		.out_a(inj_out_a_1755377830867_226),
		.out_b(inj_out_b_1755377830867_326)
	);
	recursive_param_diag_mod recursive_param_diag_mod_inst_1755377830763_4467(
		.dummy_in(inj_dummy_in_1755377830763_153),
		.out_val(inj_out_val_1755377830763_115)
	);
	split_for_loop split_for_loop_inst_1755377830637_5270(
		.start_val_i(inj_in_a_1755377830531_804),
		.sum_out_i(inj_sum_out_i_1755377830637_404),
		.clk_i(clk)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		inj_out_res_1755377830620_21 = 1'b0;
		case (inj_case_expr_1755377830490_540)
			2'b01: inj_out_res_1755377830620_21 = 1'b1;
			2'b10: inj_out_res_1755377830620_21 = 1'b0;
			default: inj_out_res_1755377830620_21 = 1'b1;
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		var_m1_ts1755377830614 = in_d;
		var_m1_ts1755377830614 = var_m1_ts1755377830614 + 1;
		inj_out_sum_m1_1755377830614_891 = var_m1_ts1755377830614 + inj_in_a_1755377830531_804;
		inj_var_out_m1_1755377830614_259 = var_m1_ts1755377830614;
	end
	ComplexConversions ComplexConversions_inst_1755377830531_3525(
		.in_b(in_d),
		.out_concat(inj_out_concat_1755377830531_635),
		.in_a(inj_in_a_1755377830531_804)
	);
	assign inj_out_1755377830528_293 = inj_enable_in_1755377830528_286;
	always @(posedge clk) q1_ts1755377830519 <= inj_a_1755377830492_285;
	always @(q1_ts1755377830519) q2_ts1755377830519 = ~q1_ts1755377830519;
	assign inj_q_out_1755377830519_395 = q2_ts1755377830519;
	assign inj_sum_1755377830492_554 = inj_a_1755377830492_285 + inj_b_1755377830492_365;
	always @(*)
		(* full_case *)
		casez (inj_case_expr_1755377830490_540)
			2'b1z: inj_internal_out_1755377830490_785 = 5;
			2'bz1: inj_internal_out_1755377830490_785 = 6;
			2'b0z: inj_internal_out_1755377830490_785 = 7;
			2'bz0: inj_internal_out_1755377830490_785 = 8;
			default: inj_internal_out_1755377830490_785 = 9;
		endcase
	CombinationalLogicImplicit CombinationalLogicImplicit_inst_1755377830490_8444(
		.a(inj_a_1755377830490_312),
		.b(inj_b_1755377830490_364),
		.sum(inj_sum_1755377830490_590)
	);
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
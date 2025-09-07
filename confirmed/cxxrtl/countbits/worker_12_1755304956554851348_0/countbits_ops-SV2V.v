module dup_expr (
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
	reg [7:0] temp_add;
	reg [7:0] temp_mult;
	reg [7:0] inter1;
	reg [7:0] inter2;
	reg [7:0] complex_expr;
	always @(*) begin
		if (_sv2v_0)
			;
		temp_add = in1 + in2;
		out1 = temp_add;
		out2 = in1 + in2;
		inter1 = in1 * 2;
		inter2 = in2 * 2;
		temp_mult = inter1 + inter2;
		complex_expr = ((in1 + in2) * (in1 - in2)) + (in1 + in2);
		if (in1 > in2)
			out1 = temp_mult;
		else
			out1 = temp_add;
		if (in2 >= in1)
			out2 = temp_add;
		else
			out2 = temp_mult;
		out1 = out1 + complex_expr;
	end
	initial _sv2v_0 = 0;
endmodule
module simple_adder (
	a,
	b,
	sum
);
	input wire a;
	input wire b;
	output wire sum;
	assign sum = a + b;
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_b_aa_1755304956884_948,
	inj_c_aa_1755304956884_870,
	inj_i_in_1755304956891_678,
	inj_in1_1755304956885_384,
	inj_in2_1755304956885_264,
	inj_sel_1755304956885_332,
	rst,
	cnt,
	inj_o_out_1755304956891_544,
	inj_out1_1755304956885_225,
	inj_out1_1755304956889_463,
	inj_out1_1755304956904_206,
	inj_out2_1755304956885_81,
	inj_out2_1755304956889_223,
	inj_x_aa_1755304956884_497,
	inj_y_aa_1755304956884_267,
	inj_z_aa_1755304956884_816
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] in_d;
	input wire [7:0] inj_b_aa_1755304956884_948;
	input wire [7:0] inj_c_aa_1755304956884_870;
	input wire inj_i_in_1755304956891_678;
	input wire [15:0] inj_in1_1755304956885_384;
	input wire [15:0] inj_in2_1755304956885_264;
	input wire inj_sel_1755304956885_332;
	input wire rst;
	output wire [3:0] cnt;
	output wire inj_o_out_1755304956891_544;
	output reg [15:0] inj_out1_1755304956885_225;
	output wire [7:0] inj_out1_1755304956889_463;
	output wire inj_out1_1755304956904_206;
	output reg [15:0] inj_out2_1755304956885_81;
	output wire [7:0] inj_out2_1755304956889_223;
	output reg [7:0] inj_x_aa_1755304956884_497;
	output reg [7:0] inj_y_aa_1755304956884_267;
	output reg [7:0] inj_z_aa_1755304956884_816;
	reg [15:0] temp1_ts1755304956885;
	reg [15:0] temp2_ts1755304956885;
	wire internal_sig_ts1755304956891;
	wire internal_sig_a_ts1755304956909;
	wire internal_sig_b_ts1755304956909;
	wire unused_line_var_ts1755304956909;
	assign internal_sig_a_ts1755304956909 = internal_sig_ts1755304956891;
	assign internal_sig_b_ts1755304956909 = ~internal_sig_a_ts1755304956909;
	assign unused_line_var_ts1755304956909 = 1'b1;
	assign inj_out1_1755304956904_206 = internal_sig_b_ts1755304956909;
	assign internal_sig_ts1755304956891 = inj_i_in_1755304956891_678 & inj_sel_1755304956885_332;
	simple_adder sa_inst(
		.a(inj_i_in_1755304956891_678),
		.b(inj_sel_1755304956885_332),
		.sum(inj_o_out_1755304956891_544)
	);
	dup_expr dup_expr_inst_1755304956889_2603(
		.out1(inj_out1_1755304956889_463),
		.out2(inj_out2_1755304956889_223),
		.in1(in_d),
		.in2(inj_b_aa_1755304956884_948)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		temp1_ts1755304956885 = (inj_in1_1755304956885_384 + inj_in2_1755304956885_264) * 10;
		if (inj_sel_1755304956885_332) begin
			temp2_ts1755304956885 = temp1_ts1755304956885 ^ (inj_in1_1755304956885_384 >>> 2);
			inj_out1_1755304956885_225 = temp2_ts1755304956885 & inj_in2_1755304956885_264;
		end
		else begin
			temp2_ts1755304956885 = temp1_ts1755304956885 | (inj_in2_1755304956885_264 <<< 3);
			inj_out1_1755304956885_225 = temp2_ts1755304956885 + inj_in1_1755304956885_384;
		end
		inj_out2_1755304956885_81 = temp1_ts1755304956885 - temp2_ts1755304956885;
	end
	always @(*) begin
		inj_x_aa_1755304956884_497 = in_d + inj_b_aa_1755304956884_948;
		inj_y_aa_1755304956884_267 = inj_x_aa_1755304956884_497 - inj_c_aa_1755304956884_870;
		inj_z_aa_1755304956884_816 = in_d * inj_c_aa_1755304956884_870;
	end
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
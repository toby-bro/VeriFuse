module ImplicitTimeScaleModule (
	in_its,
	out_its
);
	input wire in_its;
	output wire out_its;
	assign out_its = in_its;
endmodule
module ModCompareVec (
	v1,
	v2,
	eq
);
	input wire [3:0] v1;
	input wire [3:0] v2;
	output wire eq;
	assign eq = v1 == v2;
endmodule
module multi_port_decl_module (
	p_a,
	p_b,
	single_in,
	single_out
);
	reg _sv2v_0;
	input wire [3:0] p_a;
	input wire [3:0] p_b;
	input wire single_in;
	output reg single_out;
	always @(*) begin
		if (_sv2v_0)
			;
		single_out = single_in;
	end
	initial _sv2v_0 = 0;
endmodule
module split_inputs_outputs_only (
	in_val_a_l,
	in_val_b_l,
	out_val_c_l,
	out_val_d_l
);
	input wire [7:0] in_val_a_l;
	input wire [7:0] in_val_b_l;
	output reg [8:0] out_val_c_l;
	output reg [7:0] out_val_d_l;
	always @(*) begin
		out_val_c_l = in_val_a_l + in_val_b_l;
		out_val_d_l = in_val_a_l - in_val_b_l;
	end
endmodule
module packed_union_module (
	clk,
	in_data,
	inj_in_bit_1755356032427_491,
	inj_in_its_1755356032428_511,
	inj_in_q_1755356032435_222,
	inj_in_val_a_l_1755356032565_367,
	inj_in_val_b_l_1755356032565_172,
	inj_p_a_1755356032531_261,
	inj_p_b_1755356032531_46,
	rst,
	inj_byte_out_1755356032582_782,
	inj_eq_1755356032546_266,
	inj_out_data_pull0_1755356032685_599,
	inj_out_data_pull1_1755356032685_132,
	inj_out_its_1755356032428_603,
	inj_out_logic_1755356032427_789,
	inj_out_r_1755356032435_154,
	inj_out_val_c_l_1755356032565_753,
	inj_out_val_d_l_1755356032565_633,
	inj_packed_out_1755356032583_802,
	inj_single_out_1755356032531_463,
	out_data
);
	reg _sv2v_0;
	input wire clk;
	input wire [15:0] in_data;
	input wire inj_in_bit_1755356032427_491;
	input wire inj_in_its_1755356032428_511;
	input wire inj_in_q_1755356032435_222;
	input wire [7:0] inj_in_val_a_l_1755356032565_367;
	input wire [7:0] inj_in_val_b_l_1755356032565_172;
	input wire [3:0] inj_p_a_1755356032531_261;
	input wire [3:0] inj_p_b_1755356032531_46;
	input wire rst;
	output wire [7:0] inj_byte_out_1755356032582_782;
	output wire inj_eq_1755356032546_266;
	output wire inj_out_data_pull0_1755356032685_599;
	output wire inj_out_data_pull1_1755356032685_132;
	output wire inj_out_its_1755356032428_603;
	output wire inj_out_logic_1755356032427_789;
	output reg inj_out_r_1755356032435_154;
	output wire [8:0] inj_out_val_c_l_1755356032565_753;
	output wire [7:0] inj_out_val_d_l_1755356032565_633;
	output wire [15:0] inj_packed_out_1755356032583_802;
	output wire inj_single_out_1755356032531_463;
	output reg [15:0] out_data;
	reg [15:0] mydata;
	wire [15:0] data_pair;
	assign inj_out_data_pull1_1755356032685_132 = inj_in_q_1755356032435_222;
	assign inj_out_data_pull0_1755356032685_599 = ~inj_in_q_1755356032435_222;
	assign data_pair[7-:8] = in_data[15:8];
	assign data_pair[15-:8] = inj_in_val_a_l_1755356032565_367;
	assign inj_byte_out_1755356032582_782 = data_pair[7-:8];
	assign inj_packed_out_1755356032583_802[15:8] = data_pair[7-:8];
	assign inj_packed_out_1755356032583_802[7:0] = data_pair[15-:8] + inj_in_val_a_l_1755356032565_367;
	split_inputs_outputs_only split_inputs_outputs_only_inst_1755356032565_7975(
		.in_val_a_l(inj_in_val_a_l_1755356032565_367),
		.in_val_b_l(inj_in_val_b_l_1755356032565_172),
		.out_val_c_l(inj_out_val_c_l_1755356032565_753),
		.out_val_d_l(inj_out_val_d_l_1755356032565_633)
	);
	ModCompareVec ModCompareVec_inst_1755356032546_5936(
		.v2(inj_p_b_1755356032531_46),
		.eq(inj_eq_1755356032546_266),
		.v1(inj_p_a_1755356032531_261)
	);
	multi_port_decl_module multi_port_decl_module_inst_1755356032531_1418(
		.p_a(inj_p_a_1755356032531_261),
		.p_b(inj_p_b_1755356032531_46),
		.single_in(inj_in_its_1755356032428_511),
		.single_out(inj_single_out_1755356032531_463)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		inj_out_r_1755356032435_154 = inj_in_its_1755356032428_511 | inj_in_q_1755356032435_222;
	end
	ImplicitTimeScaleModule ImplicitTimeScaleModule_inst_1755356032428_9408(
		.out_its(inj_out_its_1755356032428_603),
		.in_its(inj_in_its_1755356032428_511)
	);
	assign inj_out_logic_1755356032427_789 = inj_in_bit_1755356032427_491;
	always @(*) begin
		if (_sv2v_0)
			;
		mydata[15-:16] = in_data;
		if (mydata[7])
			out_data = {8'h00, mydata[15-:8]};
		else
			out_data = {8'h00, mydata[7-:8]};
	end
	initial _sv2v_0 = 0;
endmodule
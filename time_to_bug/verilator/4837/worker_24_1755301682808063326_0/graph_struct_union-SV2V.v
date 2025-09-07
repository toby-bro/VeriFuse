module nested_blocks (
	data_value,
	level1_en,
	level2_en,
	result_out
);
	reg _sv2v_0;
	input wire data_value;
	input wire level1_en;
	input wire level2_en;
	output reg result_out;
	always @(*) begin : main_block
		if (_sv2v_0)
			;
		result_out = 1'b0;
		if (level1_en) begin : inner_block1
			if (level2_en) begin : inner_block2
				result_out = data_value;
			end
		end
	end
	initial _sv2v_0 = 0;
endmodule
module graph_struct_union (
	bus_in,
	clk,
	inj_a_1755301683265_754,
	inj_b_1755301683265_298,
	inj_data_value_1755301683149_555,
	inj_in_false_d_1755301683159_692,
	inj_in_port_1755301683145_593,
	inj_in_true_d_1755301683159_497,
	inj_level1_en_1755301683149_533,
	inj_level2_en_1755301683149_657,
	rst,
	bus_out,
	inj_out_concat_1755301683265_998,
	inj_out_port_1755301683145_366,
	inj_out_reg_d_1755301683159_117,
	inj_out_val_1755301683195_143,
	inj_result_out_1755301683149_237
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [3:0] inj_a_1755301683265_754;
	input wire [3:0] inj_b_1755301683265_298;
	input wire inj_data_value_1755301683149_555;
	input wire [7:0] inj_in_false_d_1755301683159_692;
	input wire signed [31:0] inj_in_port_1755301683145_593;
	input wire [7:0] inj_in_true_d_1755301683159_497;
	input wire inj_level1_en_1755301683149_533;
	input wire inj_level2_en_1755301683149_657;
	input wire rst;
	output wire [31:0] bus_out;
	output wire [15:0] inj_out_concat_1755301683265_998;
	output wire signed [31:0] inj_out_port_1755301683145_366;
	output reg [7:0] inj_out_reg_d_1755301683159_117;
	output wire signed [31:0] inj_out_val_1755301683195_143;
	output wire inj_result_out_1755301683149_237;
	reg [31:0] din;
	reg [31:0] dout;
	assign inj_out_concat_1755301683265_998 = {inj_a_1755301683265_754, inj_b_1755301683265_298, inj_in_false_d_1755301683159_692};
	assign inj_out_val_1755301683195_143 = 32;
	always @(posedge clk)
		if (inj_level2_en_1755301683149_657)
			inj_out_reg_d_1755301683159_117 <= inj_in_true_d_1755301683159_497;
		else
			inj_out_reg_d_1755301683159_117 <= inj_in_false_d_1755301683159_692;
	nested_blocks nested_blocks_inst_1755301683149_2222(
		.level2_en(inj_level2_en_1755301683149_657),
		.result_out(inj_result_out_1755301683149_237),
		.data_value(inj_data_value_1755301683149_555),
		.level1_en(inj_level1_en_1755301683149_533)
	);
	assign inj_out_port_1755301683145_366 = inj_in_port_1755301683145_593;
	always @(*) begin
		if (_sv2v_0)
			;
		din[31-:32] = bus_in;
		dout[31-:32] = 32'h00000000;
		dout[31-:8] = din[7-:8];
		dout[23-:8] = din[15-:8];
		dout[15-:8] = din[23-:8];
		dout[7-:8] = din[31-:8];
	end
	assign bus_out = dout[31-:32];
	initial _sv2v_0 = 0;
endmodule
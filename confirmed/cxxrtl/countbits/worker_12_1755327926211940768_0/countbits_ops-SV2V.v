module loop_with_internal_assign (
	start_val,
	final_val
);
	reg _sv2v_0;
	input wire [3:0] start_val;
	output reg [7:0] final_val;
	reg [7:0] current_val;
	always @(*) begin
		if (_sv2v_0)
			;
		current_val = start_val;
		begin : sv2v_autoblock_1
			reg signed [31:0] k;
			for (k = 0; k < 3; k = k + 1)
				current_val = current_val + 1;
		end
		final_val = current_val;
	end
	initial _sv2v_0 = 0;
endmodule
module primitive_example (
	i_p1,
	i_p2,
	o_p_and,
	o_p_xor
);
	input wire i_p1;
	input wire i_p2;
	output wire o_p_and;
	output wire o_p_xor;
	and (o_p_and, i_p1, i_p2);
	xor (o_p_xor, i_p1, i_p2);
endmodule
module wide_ops_deep (
	wide_a,
	wide_b,
	wide_c,
	wide_out
);
	input wire [63:0] wide_a;
	input wire [63:0] wide_b;
	input wire [63:0] wide_c;
	output wire [63:0] wide_out;
	assign wide_out = (((wide_a + wide_b) ^ wide_c) & (~wide_a | wide_b)) + (wide_c >>> 5);
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_data2_1755327927048_859,
	inj_data3_1755327927048_672,
	inj_data_in_1755327926991_898,
	inj_i_in_1755327926544_780,
	inj_i_p1_1755327926568_45,
	inj_i_p2_1755327926568_809,
	inj_in_data_1755327926663_217,
	inj_sel_code_1755327927048_231,
	inj_start_val_1755327926552_878,
	inj_wide_a_1755327927255_788,
	inj_wide_b_1755327927268_588,
	inj_wide_c_1755327927268_34,
	rst,
	cnt,
	inj_data_out_1755327926991_399,
	inj_final_val_1755327926552_676,
	inj_o_out_1755327926544_931,
	inj_o_p_and_1755327926568_709,
	inj_o_p_xor_1755327926568_112,
	inj_o_sum_1755327926787_322,
	inj_out1_1755327926632_57,
	inj_out2_1755327926632_351,
	inj_out_if_a_1755327927122_56,
	inj_out_if_b_1755327927122_640,
	inj_out_result_1755327926663_344,
	inj_selected_data_1755327927048_911,
	inj_wide_out_1755327927268_852,
	inj_wide_out_1755327927324_1,
	inj_wide_reg_1755327926787_940
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 8;
	input wire clk;
	input wire [7:0] in_d;
	input wire [7:0] inj_data2_1755327927048_859;
	input wire [7:0] inj_data3_1755327927048_672;
	input wire [15:0] inj_data_in_1755327926991_898;
	input wire [7:0] inj_i_in_1755327926544_780;
	input wire inj_i_p1_1755327926568_45;
	input wire inj_i_p2_1755327926568_809;
	input wire [3:0] inj_in_data_1755327926663_217;
	input wire [1:0] inj_sel_code_1755327927048_231;
	input wire [3:0] inj_start_val_1755327926552_878;
	input wire [63:0] inj_wide_a_1755327927255_788;
	input wire [63:0] inj_wide_b_1755327927268_588;
	input wire [63:0] inj_wide_c_1755327927268_34;
	input wire rst;
	output wire [3:0] cnt;
	output reg [15:0] inj_data_out_1755327926991_399;
	output wire [7:0] inj_final_val_1755327926552_676;
	output wire [7:0] inj_o_out_1755327926544_931;
	output wire inj_o_p_and_1755327926568_709;
	output wire inj_o_p_xor_1755327926568_112;
	output wire inj_o_sum_1755327926787_322;
	output wire inj_out1_1755327926632_57;
	output wire inj_out2_1755327926632_351;
	output reg [7:0] inj_out_if_a_1755327927122_56;
	output reg [7:0] inj_out_if_b_1755327927122_640;
	output reg [3:0] inj_out_result_1755327926663_344;
	output reg [7:0] inj_selected_data_1755327927048_911;
	output wire [63:0] inj_wide_out_1755327927268_852;
	output wire [63:0] inj_wide_out_1755327927324_1;
	output reg [7:0] inj_wide_reg_1755327926787_940;
	reg [WIDTH - 1:0] r_data_ts1755327926544;
	reg l_reg_ts1755327926787;
	reg [7:0] split_if_var_ts1755327927124;
	reg [7:0] other_if_var_ts1755327927124;
	assign inj_wide_out_1755327927324_1 = (((inj_wide_c_1755327927268_34 + inj_wide_b_1755327927268_588) ^ inj_wide_a_1755327927255_788) & (~inj_wide_c_1755327927268_34 | inj_wide_b_1755327927268_588)) + (inj_wide_a_1755327927255_788 >>> 5);
	wide_ops_deep wide_ops_deep_inst_1755327927268_3341(
		.wide_b(inj_wide_b_1755327927268_588),
		.wide_c(inj_wide_c_1755327927268_34),
		.wide_out(inj_wide_out_1755327927268_852),
		.wide_a(inj_wide_a_1755327927255_788)
	);
	always @(posedge clk or posedge rst)
		if (rst) begin
			split_if_var_ts1755327927124 <= 8'b00000000;
			other_if_var_ts1755327927124 <= 8'b00000000;
		end
		else if (inj_i_p2_1755327926568_809) begin
			split_if_var_ts1755327927124 <= inj_data2_1755327927048_859;
			other_if_var_ts1755327927124 <= inj_data2_1755327927048_859 + 3;
		end
		else begin
			split_if_var_ts1755327927124 <= inj_data2_1755327927048_859 - 1;
			other_if_var_ts1755327927124 <= inj_data2_1755327927048_859 - 2;
		end
	always @(*) begin
		if (_sv2v_0)
			;
		inj_out_if_a_1755327927122_56 = split_if_var_ts1755327927124;
		inj_out_if_b_1755327927122_640 = other_if_var_ts1755327927124;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		if (inj_sel_code_1755327927048_231 == 2'b00)
			inj_selected_data_1755327927048_911 = r_data_ts1755327926544;
		else if (inj_sel_code_1755327927048_231 == 2'b01)
			inj_selected_data_1755327927048_911 = in_d;
		else if (inj_sel_code_1755327927048_231 == 2'b10)
			inj_selected_data_1755327927048_911 = inj_data2_1755327927048_859;
		else
			inj_selected_data_1755327927048_911 = inj_data3_1755327927048_672;
	end
	always @(posedge clk or posedge rst)
		if (rst)
			inj_data_out_1755327926991_399 <= 16'h0000;
		else
			inj_data_out_1755327926991_399 <= inj_data_in_1755327926991_898;
	always @(*) begin
		if (_sv2v_0)
			;
		l_reg_ts1755327926787 = 1;
		inj_wide_reg_1755327926787_940 = {clk, rst};
	end
	assign inj_o_sum_1755327926787_322 = clk + rst;
	always @(*) begin
		if (_sv2v_0)
			;
		if (inj_in_data_1755327926663_217 > 8)
			inj_out_result_1755327926663_344 = inj_in_data_1755327926663_217 + 1;
		else
			inj_out_result_1755327926663_344 = inj_in_data_1755327926663_217 - 1;
	end
	reg [1:0] data_ua [0:1];
	always @(*) begin
		if (_sv2v_0)
			;
		data_ua[0][0] = inj_i_p1_1755327926568_45;
		data_ua[0][1] = inj_i_p2_1755327926568_809;
		data_ua[1][0] = data_ua[0][0];
		data_ua[1][1] = ~data_ua[0][1];
	end
	assign inj_out1_1755327926632_57 = data_ua[1][0];
	assign inj_out2_1755327926632_351 = data_ua[1][1];
	primitive_example primitive_example_inst_1755327926568_8370(
		.o_p_xor(inj_o_p_xor_1755327926568_112),
		.i_p1(inj_i_p1_1755327926568_45),
		.i_p2(inj_i_p2_1755327926568_809),
		.o_p_and(inj_o_p_and_1755327926568_709)
	);
	loop_with_internal_assign loop_with_internal_assign_inst_1755327926552_4898(
		.final_val(inj_final_val_1755327926552_676),
		.start_val(inj_start_val_1755327926552_878)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		r_data_ts1755327926544 = inj_i_in_1755327926544_780;
	end
	assign inj_o_out_1755327926544_931 = r_data_ts1755327926544;
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
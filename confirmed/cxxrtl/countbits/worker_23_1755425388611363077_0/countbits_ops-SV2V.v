module simple_logic_a (
	data_a,
	data_b
);
	input wire data_a;
	output wire data_b;
	assign data_b = ~data_a;
endmodule
module split_vector_assign (
	clk_y,
	condition_y,
	in_val_y,
	out_vec_y
);
	input wire clk_y;
	input wire condition_y;
	input wire [7:0] in_val_y;
	output reg [7:0] out_vec_y;
	always @(posedge clk_y)
		if (condition_y) begin
			out_vec_y[3:0] <= in_val_y[3:0];
			out_vec_y[7:4] <= in_val_y[7:4] + 1;
		end
		else
			out_vec_y <= 8'hff;
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_condition_y_1755425388970_81,
	inj_in_val_1755425388934_179,
	rst,
	cnt,
	inj_data_b_1755425388969_538,
	inj_out_res_1755425388934_531,
	inj_out_vec_y_1755425388970_237
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] in_d;
	input wire inj_condition_y_1755425388970_81;
	input wire [2:0] inj_in_val_1755425388934_179;
	input wire rst;
	output wire [3:0] cnt;
	output wire inj_data_b_1755425388969_538;
	output reg inj_out_res_1755425388934_531;
	output wire [7:0] inj_out_vec_y_1755425388970_237;
	split_vector_assign split_vector_assign_inst_1755425388970_2889(
		.in_val_y(in_d),
		.out_vec_y(inj_out_vec_y_1755425388970_237),
		.clk_y(clk),
		.condition_y(inj_condition_y_1755425388970_81)
	);
	simple_logic_a simple_logic_a_inst_1755425388969_7288(
		.data_a(clk),
		.data_b(inj_data_b_1755425388969_538)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		inj_out_res_1755425388934_531 = 1'b0;
		casez (inj_in_val_1755425388934_179)
			3'b1zz: inj_out_res_1755425388934_531 = 1'b1;
			3'b0zz: inj_out_res_1755425388934_531 = 1'b0;
			default: inj_out_res_1755425388934_531 = 1'b1;
		endcase
	end
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
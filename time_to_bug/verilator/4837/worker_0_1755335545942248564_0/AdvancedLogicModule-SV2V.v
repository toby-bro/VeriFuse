module ConcatVectorOps (
	a,
	b,
	c,
	out_concat
);
	input wire [3:0] a;
	input wire [3:0] b;
	input wire [7:0] c;
	output wire [15:0] out_concat;
	assign out_concat = {a, b, c};
endmodule
module SimpleLoopExample (
	in_vec,
	out_vec
);
	reg _sv2v_0;
	input wire [7:0] in_vec;
	output reg [7:0] out_vec;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < 8; i = i + 1)
				out_vec[i] = in_vec[7 - i];
		end
	end
	initial _sv2v_0 = 0;
endmodule
module mod_simple_ref (
	i_data,
	o_result
);
	reg _sv2v_0;
	input wire i_data;
	output reg o_result;
	reg internal_sig;
	always @(*) begin
		if (_sv2v_0)
			;
		internal_sig = i_data;
		o_result = internal_sig;
	end
	initial _sv2v_0 = 0;
endmodule
module split_multiple_in_branch (
	clk_j,
	condition_j,
	in_a_j,
	in_b_j,
	out_x_j,
	out_y_j
);
	input wire clk_j;
	input wire condition_j;
	input wire [7:0] in_a_j;
	input wire [7:0] in_b_j;
	output reg [7:0] out_x_j;
	output reg [7:0] out_y_j;
	always @(posedge clk_j)
		if (condition_j) begin
			out_x_j <= in_a_j * 3;
			out_y_j <= in_b_j + 1;
		end
		else begin
			out_x_j <= in_a_j;
			out_y_j <= in_b_j;
		end
endmodule
module AdvancedLogicModule (
	clk,
	data_in_a,
	data_in_b,
	inj_b_1755335546256_464,
	inj_i_data_1755335546263_189,
	rst,
	select_in,
	inj_o_result_1755335546263_785,
	inj_out_concat_1755335546256_836,
	inj_out_vec_1755335546262_949,
	inj_out_x_j_1755335546271_23,
	inj_out_y_j_1755335546271_512,
	result_out
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] data_in_a;
	input wire [7:0] data_in_b;
	input wire [3:0] inj_b_1755335546256_464;
	input wire inj_i_data_1755335546263_189;
	input wire rst;
	input wire [3:0] select_in;
	output wire inj_o_result_1755335546263_785;
	output wire [15:0] inj_out_concat_1755335546256_836;
	output wire [7:0] inj_out_vec_1755335546262_949;
	output wire [7:0] inj_out_x_j_1755335546271_23;
	output wire [7:0] inj_out_y_j_1755335546271_512;
	output reg [7:0] result_out;
	reg [31:0] current_op;
	function automatic [7:0] calculate_sum;
		input reg [7:0] a;
		input reg [7:0] b;
		calculate_sum = a + b;
	endfunction
	task automatic update_result;
		input reg [7:0] val_a;
		input reg [7:0] val_b;
		output reg [7:0] res;
		res = val_a ^ val_b;
	endtask
	reg [7:0] temp_res;
	split_multiple_in_branch split_multiple_in_branch_inst_1755335546271_2591(
		.out_x_j(inj_out_x_j_1755335546271_23),
		.out_y_j(inj_out_y_j_1755335546271_512),
		.clk_j(clk),
		.condition_j(inj_i_data_1755335546263_189),
		.in_a_j(data_in_b),
		.in_b_j(data_in_a)
	);
	mod_simple_ref mod_simple_ref_inst_1755335546263_6350(
		.i_data(inj_i_data_1755335546263_189),
		.o_result(inj_o_result_1755335546263_785)
	);
	SimpleLoopExample SimpleLoopExample_inst_1755335546262_5918(
		.in_vec(data_in_a),
		.out_vec(inj_out_vec_1755335546262_949)
	);
	ConcatVectorOps ConcatVectorOps_inst_1755335546256_2898(
		.a(select_in),
		.b(inj_b_1755335546256_464),
		.c(data_in_a),
		.out_concat(inj_out_concat_1755335546256_836)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (select_in)
			4'b0000: current_op = 32'd0;
			4'b0001: current_op = 32'd1;
			4'b0010: current_op = 32'd2;
			4'b0011: current_op = 32'd3;
			default: current_op = 32'd0;
		endcase
		if (current_op == 32'd0)
			result_out = calculate_sum(data_in_a, data_in_b);
		else if (current_op == 32'd1)
			result_out = data_in_a - data_in_b;
		else if (current_op == 32'd2)
			result_out = data_in_a * data_in_b;
		else if (current_op == 32'd3) begin
			if (data_in_b != 0)
				result_out = data_in_a / data_in_b;
			else
				result_out = 1'sb0;
		end
		else
			result_out = 1'sb0;
		update_result(data_in_a, data_in_b, temp_res);
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < 4; i = i + 1)
				temp_res[i] = temp_res[i] ^ data_in_a[i + 4];
		end
	end
	always @(*)
		if (_sv2v_0)
			;
	initial _sv2v_0 = 0;
endmodule
module BitwiseOperations (
	a,
	b,
	c,
	result_and,
	result_or,
	result_xor
);
	input wire [7:0] a;
	input wire [7:0] b;
	input wire [7:0] c;
	output wire [7:0] result_and;
	output wire [7:0] result_or;
	output wire [7:0] result_xor;
	assign result_and = a & b;
	assign result_or = a | c;
	assign result_xor = b ^ c;
endmodule
module basic_assign_if (
	in_a,
	in_b,
	out_c
);
	reg _sv2v_0;
	input wire in_a;
	input wire in_b;
	output reg out_c;
	wire intermediate_wire;
	assign intermediate_wire = in_a & in_b;
	always @(*) begin
		if (_sv2v_0)
			;
		if (intermediate_wire)
			out_c = 1'b1;
		else
			out_c = 1'b0;
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
module module_sequential_writes (
	addr,
	wdata,
	write_status
);
	reg _sv2v_0;
	input wire [7:0] addr;
	input wire [7:0] wdata;
	output reg write_status;
	generate
		if (1) begin : vif_bus
			reg [7:0] data;
			reg ready;
			reg valid;
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		vif_bus.data = wdata;
		vif_bus.ready = 1'b1;
		vif_bus.valid = 1'b0;
		write_status = vif_bus.ready;
	end
	initial _sv2v_0 = 0;
endmodule
module split_mixed_cond_seq (
	clk_e,
	condition_e,
	in_override_e,
	in_val_e,
	out_val_e,
	status_e
);
	input wire clk_e;
	input wire condition_e;
	input wire [7:0] in_override_e;
	input wire [7:0] in_val_e;
	output reg [7:0] out_val_e;
	output reg status_e;
	reg [7:0] temp_val_e;
	always @(posedge clk_e) begin
		temp_val_e <= in_val_e + 5;
		if (condition_e) begin
			out_val_e <= temp_val_e;
			status_e <= 1;
		end
		else begin
			out_val_e <= in_override_e;
			status_e <= 0;
		end
	end
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
module countbits_ops (
	clk,
	in_d,
	inj_c_1755327926877_515,
	inj_condition_m10_1755327926899_772,
	inj_in_a_1755327926597_456,
	inj_in_b_1755327926597_288,
	inj_in_val_1755327926679_968,
	inj_in_val_1755327927134_292,
	inj_wdata_1755327926605_780,
	inj_wide_a_1755327927347_668,
	inj_wide_b_1755327927347_670,
	rst,
	cnt,
	inj_concat_out_1755327927347_427,
	inj_o_1755327927318_827,
	inj_out_a_1755327926996_303,
	inj_out_c_1755327926597_759,
	inj_out_l_1755327927422_888,
	inj_out_res_1755327927134_581,
	inj_out_val_1755327926679_899,
	inj_out_val_e_1755327926794_252,
	inj_out_val_m10_1755327926899_456,
	inj_q_1755327926598_87,
	inj_reduce_xor_out_1755327927347_628,
	inj_result_and_1755327926877_946,
	inj_result_and_1755327927243_949,
	inj_result_or_1755327926877_344,
	inj_result_or_1755327927243_40,
	inj_result_xor_1755327926877_731,
	inj_result_xor_1755327927243_76,
	inj_status_e_1755327926794_433,
	inj_tok_out_1755327926900_192,
	inj_wide_sum_1755327927347_424,
	inj_write_status_1755327926605_259
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] in_d;
	input wire [7:0] inj_c_1755327926877_515;
	input wire inj_condition_m10_1755327926899_772;
	input wire inj_in_a_1755327926597_456;
	input wire inj_in_b_1755327926597_288;
	input wire signed [31:0] inj_in_val_1755327926679_968;
	input wire [1:0] inj_in_val_1755327927134_292;
	input wire [7:0] inj_wdata_1755327926605_780;
	input wire [63:0] inj_wide_a_1755327927347_668;
	input wire [63:0] inj_wide_b_1755327927347_670;
	input wire rst;
	output wire [3:0] cnt;
	output wire [127:0] inj_concat_out_1755327927347_427;
	output wire inj_o_1755327927318_827;
	output wire inj_out_a_1755327926996_303;
	output wire inj_out_c_1755327926597_759;
	output reg inj_out_l_1755327927422_888;
	output reg inj_out_res_1755327927134_581;
	output wire signed [31:0] inj_out_val_1755327926679_899;
	output wire [7:0] inj_out_val_e_1755327926794_252;
	output wire [7:0] inj_out_val_m10_1755327926899_456;
	output reg inj_q_1755327926598_87;
	output wire [7:0] inj_reduce_xor_out_1755327927347_628;
	output wire [7:0] inj_result_and_1755327926877_946;
	output wire [7:0] inj_result_and_1755327927243_949;
	output wire [7:0] inj_result_or_1755327926877_344;
	output wire [7:0] inj_result_or_1755327927243_40;
	output wire [7:0] inj_result_xor_1755327926877_731;
	output wire [7:0] inj_result_xor_1755327927243_76;
	output wire inj_status_e_1755327926794_433;
	output reg inj_tok_out_1755327926900_192;
	output wire [63:0] inj_wide_sum_1755327927347_424;
	output wire inj_write_status_1755327926605_259;
	always @(*) begin
		if (_sv2v_0)
			;
		if (inj_in_b_1755327926597_288)
			inj_out_l_1755327927422_888 = inj_in_a_1755327926597_456;
		else
			inj_out_l_1755327927422_888 = 1'b0;
	end
	assign inj_wide_sum_1755327927347_424 = inj_wide_a_1755327927347_668 + inj_wide_b_1755327927347_670;
	assign inj_reduce_xor_out_1755327927347_628 = ^inj_wide_a_1755327927347_668[63:0];
	assign inj_concat_out_1755327927347_427 = {inj_wide_a_1755327927347_668, inj_wide_b_1755327927347_670};
	buf b1 (inj_o_1755327927318_827, clk);
	BitwiseOperations BitwiseOperations_inst_1755327927243_998(
		.a(inj_c_1755327926877_515),
		.b(inj_wdata_1755327926605_780),
		.c(in_d),
		.result_and(inj_result_and_1755327927243_949),
		.result_or(inj_result_or_1755327927243_40),
		.result_xor(inj_result_xor_1755327927243_76)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		inj_out_res_1755327927134_581 = 1'b0;
		case (inj_in_val_1755327927134_292)
			2'b00: inj_out_res_1755327927134_581 = 1'b1;
			2'b01:
				;
			2'b10: inj_out_res_1755327927134_581 = 1'b0;
			default: inj_out_res_1755327927134_581 = 1'b1;
		endcase
	end
	mod_name_conflict mod_name_conflict_inst_1755327926996_9780(
		.in_a(inj_in_a_1755327926597_456),
		.out_a(inj_out_a_1755327926996_303)
	);
	reg my_var;
	always @(*) begin
		if (_sv2v_0)
			;
		my_var = inj_in_b_1755327926597_288;
		inj_tok_out_1755327926900_192 = my_var;
	end
	unsupported_cond_expr unsupported_cond_expr_inst_1755327926899_72(
		.out_val_m10(inj_out_val_m10_1755327926899_456),
		.condition_m10(inj_condition_m10_1755327926899_772),
		.in_val_m10(inj_wdata_1755327926605_780)
	);
	assign inj_result_and_1755327926877_946 = in_d & inj_wdata_1755327926605_780;
	assign inj_result_or_1755327926877_344 = in_d | inj_c_1755327926877_515;
	assign inj_result_xor_1755327926877_731 = inj_wdata_1755327926605_780 ^ inj_c_1755327926877_515;
	split_mixed_cond_seq split_mixed_cond_seq_inst_1755327926794_2914(
		.condition_e(inj_in_a_1755327926597_456),
		.in_override_e(inj_wdata_1755327926605_780),
		.in_val_e(in_d),
		.out_val_e(inj_out_val_e_1755327926794_252),
		.status_e(inj_status_e_1755327926794_433),
		.clk_e(clk)
	);
	assign inj_out_val_1755327926679_899 = inj_in_val_1755327926679_968;
	module_sequential_writes module_sequential_writes_inst_1755327926605_4777(
		.write_status(inj_write_status_1755327926605_259),
		.addr(in_d),
		.wdata(inj_wdata_1755327926605_780)
	);
	always @(posedge clk or negedge rst)
		if (!rst)
			inj_q_1755327926598_87 <= 1'b0;
		else
			inj_q_1755327926598_87 <= inj_in_a_1755327926597_456;
	basic_assign_if basic_assign_if_inst_1755327926597_6165(
		.in_a(inj_in_a_1755327926597_456),
		.in_b(inj_in_b_1755327926597_288),
		.out_c(inj_out_c_1755327926597_759)
	);
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
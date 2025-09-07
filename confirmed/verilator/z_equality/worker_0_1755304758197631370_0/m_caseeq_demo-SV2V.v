module case_default (
	in_val,
	out_res
);
	reg _sv2v_0;
	input wire [1:0] in_val;
	output reg out_res;
	always @(*) begin
		if (_sv2v_0)
			;
		out_res = 1'b0;
		case (in_val)
			2'b01: out_res = 1'b1;
			2'b10: out_res = 1'b0;
			default: out_res = 1'b1;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module dup_cond (
	control,
	data_a,
	data_b,
	result1,
	result2
);
	reg _sv2v_0;
	input wire [3:0] control;
	input wire [7:0] data_a;
	input wire [7:0] data_b;
	output reg [7:0] result1;
	output reg [7:0] result2;
	always @(*) begin
		if (_sv2v_0)
			;
		result1 = 1'sb0;
		result2 = 1'sb0;
		if (control[0])
			result1 = data_a + data_b;
		else
			result1 = data_a - data_b;
		if (control[1])
			result2 = data_a - data_b;
		else
			result2 = data_a + data_b;
		case (control[3:2])
			2'b00: result1 = data_a & data_b;
			2'b01: result1 = data_a | data_b;
			2'b10: result2 = data_a & data_b;
			2'b11: result2 = data_a | data_b;
			default: begin
				result1 = 1'sb0;
				result2 = 1'sb0;
			end
		endcase
		if (control[0] == control[1])
			result1 = result1 + 1;
		else if (control[2] != control[3])
			result2 = result2 - 1;
	end
	initial _sv2v_0 = 0;
endmodule
module param_local_port (
	i_reset,
	o_sum
);
	reg _sv2v_0;
	parameter signed [31:0] P_PORT_VAL = 25;
	input wire i_reset;
	output reg [7:0] o_sum;
	localparam signed [31:0] LP_BODY_VAL = 125;
	localparam signed [31:0] LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
	always @(*) begin
		if (_sv2v_0)
			;
		if (i_reset)
			o_sum = 0;
		else
			o_sum = LP_CALCULATED;
	end
	initial _sv2v_0 = 0;
endmodule
module m_caseeq_demo (
	clk,
	in,
	inj_control_1755304758505_57,
	inj_data_a_1755304758505_682,
	inj_data_b_1755304758505_655,
	inj_in_val_1755304758570_619,
	rst,
	eq,
	inj_o_sum_1755304758694_598,
	inj_out_b_1755304758633_602,
	inj_out_res_1755304758570_971,
	inj_result1_1755304758505_998,
	inj_result2_1755304758505_658,
	neq
);
	input wire clk;
	input wire in;
	input wire [3:0] inj_control_1755304758505_57;
	input wire [7:0] inj_data_a_1755304758505_682;
	input wire [7:0] inj_data_b_1755304758505_655;
	input wire [1:0] inj_in_val_1755304758570_619;
	input wire rst;
	output wire eq;
	output wire [7:0] inj_o_sum_1755304758694_598;
	output wire inj_out_b_1755304758633_602;
	output reg inj_out_res_1755304758570_971;
	output wire [7:0] inj_result1_1755304758505_998;
	output wire [7:0] inj_result2_1755304758505_658;
	output wire neq;
	reg tri_sig = 1'bz;
	wire unused_w_ts1755304758633;
	param_local_port param_local_port_inst_1755304758694_5650(
		.i_reset(rst),
		.o_sum(inj_o_sum_1755304758694_598)
	);
	assign inj_out_b_1755304758633_602 = in;
	wire [1:1] sv2v_tmp_case_default_inst_1755304758570_8438_out_res;
	always @(*) inj_out_res_1755304758570_971 = sv2v_tmp_case_default_inst_1755304758570_8438_out_res;
	case_default case_default_inst_1755304758570_8438(
		.in_val(inj_in_val_1755304758570_619),
		.out_res(sv2v_tmp_case_default_inst_1755304758570_8438_out_res)
	);
	dup_cond dup_cond_inst_1755304758505_2928(
		.control(inj_control_1755304758505_57),
		.data_a(inj_data_a_1755304758505_682),
		.data_b(inj_data_b_1755304758505_655),
		.result1(inj_result1_1755304758505_998),
		.result2(inj_result2_1755304758505_658)
	);
	assign eq = in === tri_sig;
	assign neq = in !== tri_sig;
endmodule
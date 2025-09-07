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
module case_parallel_simple_mod (
	case_inside_val,
	internal_out
);
	input wire [3:0] case_inside_val;
	output reg [4:0] internal_out;
	always @(*)
		(* parallel *)
		case (case_inside_val)
			4'd0, 4'd1: internal_out = 14;
			4'd2, 4'd3: internal_out = 15;
			default: internal_out = 18;
		endcase
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_case_inside_val_1755377830573_7,
	inj_in_a_1755377830652_305,
	inj_in_b_1755377830652_350,
	inj_p_in1_1755377830570_818,
	inj_p_in2_1755377830570_72,
	inj_p_mode_1755377830570_231,
	rst,
	cnt,
	inj_internal_out_1755377830573_477,
	inj_out_c_1755377830652_372,
	inj_p_out_1755377830570_901
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] in_d;
	input wire [3:0] inj_case_inside_val_1755377830573_7;
	input wire inj_in_a_1755377830652_305;
	input wire inj_in_b_1755377830652_350;
	input wire [31:0] inj_p_in1_1755377830570_818;
	input wire [31:0] inj_p_in2_1755377830570_72;
	input wire [1:0] inj_p_mode_1755377830570_231;
	input wire rst;
	output wire [3:0] cnt;
	output wire [4:0] inj_internal_out_1755377830573_477;
	output wire inj_out_c_1755377830652_372;
	output reg [31:0] inj_p_out_1755377830570_901;
	basic_assign_if basic_assign_if_inst_1755377830652_7210(
		.in_a(inj_in_a_1755377830652_305),
		.in_b(inj_in_b_1755377830652_350),
		.out_c(inj_out_c_1755377830652_372)
	);
	case_parallel_simple_mod case_parallel_simple_mod_inst_1755377830573_2267(
		.case_inside_val(inj_case_inside_val_1755377830573_7),
		.internal_out(inj_internal_out_1755377830573_477)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		case (inj_p_mode_1755377830570_231)
			2'b00: inj_p_out_1755377830570_901 = (inj_p_in1_1755377830570_818 + inj_p_in2_1755377830570_72) * 2;
			2'b01: inj_p_out_1755377830570_901 = (inj_p_in1_1755377830570_818 - inj_p_in2_1755377830570_72) / 3;
			2'b10: inj_p_out_1755377830570_901 = (inj_p_in1_1755377830570_818 << 4) | (inj_p_in2_1755377830570_72 >> 2);
			default: inj_p_out_1755377830570_901 = ~(inj_p_in1_1755377830570_818 ^ inj_p_in2_1755377830570_72) + 1;
		endcase
	end
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
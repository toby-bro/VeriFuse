module case_priority_overlapping_mod (
	case_expr,
	internal_out
);
	input wire [1:0] case_expr;
	output reg [4:0] internal_out;
	always @(*)
		(* full_case *)
		casez (case_expr)
			2'b1z: internal_out = 5;
			2'bz1: internal_out = 6;
			2'b0z: internal_out = 7;
			2'bz0: internal_out = 8;
			default: internal_out = 9;
		endcase
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_case_expr_1755425388977_720,
	inj_shift_val_1755425388976_868,
	rst,
	cnt,
	inj_internal_out_1755425388977_412,
	inj_left_shift_log_1755425388976_490,
	inj_right_shift_arith_1755425388976_438,
	inj_right_shift_log_1755425388976_946
);
	input wire clk;
	input wire [7:0] in_d;
	input wire [1:0] inj_case_expr_1755425388977_720;
	input wire [2:0] inj_shift_val_1755425388976_868;
	input wire rst;
	output wire [3:0] cnt;
	output wire [4:0] inj_internal_out_1755425388977_412;
	output wire [7:0] inj_left_shift_log_1755425388976_490;
	output wire [7:0] inj_right_shift_arith_1755425388976_438;
	output wire [7:0] inj_right_shift_log_1755425388976_946;
	case_priority_overlapping_mod case_priority_overlapping_mod_inst_1755425388977_1590(
		.internal_out(inj_internal_out_1755425388977_412),
		.case_expr(inj_case_expr_1755425388977_720)
	);
	assign inj_left_shift_log_1755425388976_490 = in_d << inj_shift_val_1755425388976_868;
	assign inj_right_shift_log_1755425388976_946 = in_d >> inj_shift_val_1755425388976_868;
	assign inj_right_shift_arith_1755425388976_438 = $signed(in_d) >>> inj_shift_val_1755425388976_868;
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule
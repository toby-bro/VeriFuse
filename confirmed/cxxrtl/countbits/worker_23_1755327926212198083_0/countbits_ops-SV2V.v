module deep_comb_assign_chain (
	dcac_start_val,
	dcac_end_val
);
	reg _sv2v_0;
	input wire [15:0] dcac_start_val;
	output reg [15:0] dcac_end_val;
	reg [15:0] t1;
	reg [15:0] t2;
	reg [15:0] t3;
	reg [15:0] t4;
	reg [15:0] t5;
	reg [15:0] t6;
	reg [15:0] t7;
	reg [15:0] t8;
	reg [15:0] t9;
	reg [15:0] t10;
	reg [15:0] t11;
	reg [15:0] t12;
	reg [15:0] t13;
	reg [15:0] t14;
	reg [15:0] t15;
	reg [15:0] t16;
	reg [15:0] t17;
	reg [15:0] t18;
	reg [15:0] t19;
	reg [15:0] t20;
	reg [15:0] t21;
	reg [15:0] t22;
	reg [15:0] t23;
	reg [15:0] t24;
	reg [15:0] t25;
	reg [15:0] t26;
	reg [15:0] t27;
	reg [15:0] t28;
	reg [15:0] t29;
	reg [15:0] t30;
	reg [15:0] t31;
	reg [15:0] t32;
	reg [15:0] t33;
	reg [15:0] t34;
	reg [15:0] t35;
	reg [15:0] t36;
	reg [15:0] t37;
	reg [15:0] t38;
	reg [15:0] t39;
	reg [15:0] t40;
	always @(*) begin
		if (_sv2v_0)
			;
		t1 = dcac_start_val + 1;
		t2 = t1 * 2;
		t3 = t2 - 3;
		t4 = t3 ^ 4;
		t5 = t4 | 5;
		t6 = t5 & 6;
		t7 = t6 + 7;
		t8 = t7 - 8;
		t9 = t8 ^ 9;
		t10 = t9 | 10;
		t11 = t10 & 11;
		t12 = t11 + 12;
		t13 = t12 - 13;
		t14 = t13 ^ 14;
		t15 = t14 | 15;
		t16 = t15 + 16;
		t17 = t16 * 17;
		t18 = t17 - 18;
		t19 = t18 ^ 19;
		t20 = t19 | 20;
		t21 = t20 + 1;
		t22 = t21 * 2;
		t23 = t22 - 3;
		t24 = t23 ^ 4;
		t25 = t24 | 5;
		t26 = t25 & 6;
		t27 = t26 + 7;
		t28 = t27 - 8;
		t29 = t28 ^ 9;
		t30 = t29 | 10;
		t31 = t30 & 11;
		t32 = t31 + 12;
		t33 = t32 - 13;
		t34 = t33 ^ 14;
		t35 = t34 | 15;
		t36 = t35 + 16;
		t37 = t36 * 17;
		t38 = t37 - 18;
		t39 = t38 ^ 19;
		t40 = t39 | 20;
		dcac_end_val = t40;
	end
	initial _sv2v_0 = 0;
endmodule
module mod_event_implicit (
	data_in,
	data_out
);
	input wire [3:0] data_in;
	output reg [3:0] data_out;
	always @(*) data_out = data_in;
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
	inj_a_1755327926594_927,
	inj_b_1755327926594_559,
	inj_data_in_1755327926602_730,
	inj_in_packed_data_1755327926592_863,
	rst,
	cnt,
	inj_data_out_1755327926602_312,
	inj_dcac_end_val_1755327926620_215,
	inj_out_byte_1755327926592_216,
	inj_sig_out_1755327926769_346,
	inj_sum_1755327926594_173
);
	parameter [0:0] GEN = 1;
	input wire clk;
	input wire [7:0] in_d;
	input wire inj_a_1755327926594_927;
	input wire inj_b_1755327926594_559;
	input wire [3:0] inj_data_in_1755327926602_730;
	input wire [15:0] inj_in_packed_data_1755327926592_863;
	input wire rst;
	output wire [3:0] cnt;
	output reg [3:0] inj_data_out_1755327926602_312;
	output wire [15:0] inj_dcac_end_val_1755327926620_215;
	output wire [7:0] inj_out_byte_1755327926592_216;
	output wire inj_sig_out_1755327926769_346;
	output wire inj_sum_1755327926594_173;
	wire [15:0] data_struct;
	generate
		if (GEN) begin : g_true
			assign inj_sig_out_1755327926769_346 = inj_a_1755327926594_927;
		end
		else begin : g_false
			assign inj_sig_out_1755327926769_346 = ~inj_a_1755327926594_927;
		end
	endgenerate
	deep_comb_assign_chain deep_comb_assign_chain_inst_1755327926620_1118(
		.dcac_end_val(inj_dcac_end_val_1755327926620_215),
		.dcac_start_val(inj_in_packed_data_1755327926592_863)
	);
	wire [4:1] sv2v_tmp_mod_event_implicit_inst_1755327926602_5403_data_out;
	always @(*) inj_data_out_1755327926602_312 = sv2v_tmp_mod_event_implicit_inst_1755327926602_5403_data_out;
	mod_event_implicit mod_event_implicit_inst_1755327926602_5403(
		.data_out(sv2v_tmp_mod_event_implicit_inst_1755327926602_5403_data_out),
		.data_in(inj_data_in_1755327926602_730)
	);
	simple_adder simple_adder_inst_1755327926594_5289(
		.b(inj_b_1755327926594_559),
		.sum(inj_sum_1755327926594_173),
		.a(inj_a_1755327926594_927)
	);
	assign data_struct = inj_in_packed_data_1755327926592_863;
	assign inj_out_byte_1755327926592_216 = data_struct[15-:8];
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule
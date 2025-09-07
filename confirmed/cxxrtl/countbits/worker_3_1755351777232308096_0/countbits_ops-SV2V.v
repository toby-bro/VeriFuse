module ansi_basic (
	clk,
	reset_n
);
	reg _sv2v_0;
	input wire clk;
	output reg reset_n;
	always @(*) begin
		if (_sv2v_0)
			;
		reset_n = clk;
	end
	initial _sv2v_0 = 0;
endmodule
module multiplexer_2to1 (
	data0,
	data1,
	sel,
	result
);
	input wire data0;
	input wire data1;
	input wire sel;
	output wire result;
	assign result = (sel ? data1 : data0);
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_data0_1755351777564_99,
	inj_data1_1755351777564_71,
	inj_sel_1755351777564_214,
	rst,
	cnt,
	inj_reset_n_1755351777563_896,
	inj_result_1755351777564_750
);
	input wire clk;
	input wire [7:0] in_d;
	input wire inj_data0_1755351777564_99;
	input wire inj_data1_1755351777564_71;
	input wire inj_sel_1755351777564_214;
	input wire rst;
	output wire [3:0] cnt;
	output wire inj_reset_n_1755351777563_896;
	output wire inj_result_1755351777564_750;
	multiplexer_2to1 multiplexer_2to1_inst_1755351777564_1416(
		.result(inj_result_1755351777564_750),
		.data0(inj_data0_1755351777564_99),
		.data1(inj_data1_1755351777564_71),
		.sel(inj_sel_1755351777564_214)
	);
	ansi_basic ansi_basic_inst_1755351777563_2791(
		.clk(clk),
		.reset_n(inj_reset_n_1755351777563_896)
	);
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule
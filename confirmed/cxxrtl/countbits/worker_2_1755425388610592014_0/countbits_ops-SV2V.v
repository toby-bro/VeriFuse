module countbits_ops (
	clk,
	in_d,
	rst,
	cnt,
	inj_out2_a_1755425388951_811
);
	input wire clk;
	input wire [7:0] in_d;
	input wire rst;
	output wire [3:0] cnt;
	output reg [7:0] inj_out2_a_1755425388951_811;
	always @(posedge clk) inj_out2_a_1755425388951_811 <= in_d;
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule
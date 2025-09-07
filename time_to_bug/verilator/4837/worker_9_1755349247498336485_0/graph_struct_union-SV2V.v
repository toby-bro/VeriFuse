module graph_struct_union (
	bus_in,
	clk,
	inj_in_data_1755349247825_180,
	rst,
	bus_out,
	inj_out_bits_1755349247825_572
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [7:0] inj_in_data_1755349247825_180;
	input wire rst;
	output wire [31:0] bus_out;
	output reg [1:0] inj_out_bits_1755349247825_572;
	reg [31:0] din;
	reg [31:0] dout;
	reg [7:0] internal_ts1755349247826;
	always @(*) begin
		if (_sv2v_0)
			;
		internal_ts1755349247826 = inj_in_data_1755349247825_180;
		inj_out_bits_1755349247825_572 = internal_ts1755349247826[3-:2];
	end
	always @(*) begin
		if (_sv2v_0)
			;
		din[31-:32] = bus_in;
		dout[31-:32] = 32'h00000000;
		dout[31-:8] = din[7-:8];
		dout[23-:8] = din[15-:8];
		dout[15-:8] = din[23-:8];
		dout[7-:8] = din[31-:8];
	end
	assign bus_out = dout[31-:32];
	initial _sv2v_0 = 0;
endmodule
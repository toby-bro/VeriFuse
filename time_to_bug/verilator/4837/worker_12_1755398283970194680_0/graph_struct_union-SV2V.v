module graph_struct_union (
	bus_in,
	clk,
	inj_en_1755398284271_120,
	inj_in1_1755398284270_206,
	inj_in2_1755398284270_577,
	rst,
	bus_out,
	inj_data_out_1755398284271_538,
	inj_out1_1755398284270_451
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire inj_en_1755398284271_120;
	input wire [7:0] inj_in1_1755398284270_206;
	input wire [7:0] inj_in2_1755398284270_577;
	input wire rst;
	output wire [31:0] bus_out;
	output reg [7:0] inj_data_out_1755398284271_538;
	output reg [7:0] inj_out1_1755398284270_451;
	reg [31:0] din;
	reg [31:0] dout;
	wire [7:0] temp_wire_ts1755398284270;
	always @(posedge clk)
		if (inj_en_1755398284271_120)
			inj_data_out_1755398284271_538 <= inj_in2_1755398284270_577;
	assign temp_wire_ts1755398284270 = inj_in1_1755398284270_206 + inj_in2_1755398284270_577;
	always @(*) begin
		if (_sv2v_0)
			;
		inj_out1_1755398284270_451 = temp_wire_ts1755398284270;
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
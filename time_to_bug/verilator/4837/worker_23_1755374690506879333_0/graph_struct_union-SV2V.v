module graph_struct_union (
	bus_in,
	clk,
	inj_data_in_1755374690838_411,
	inj_en_1755374690838_231,
	inj_packed_in_1755374690832_418,
	rst,
	bus_out,
	inj_data_out_1755374690838_314,
	inj_field0_byte_o_1755374690832_197
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [7:0] inj_data_in_1755374690838_411;
	input wire inj_en_1755374690838_231;
	input wire [15:0] inj_packed_in_1755374690832_418;
	input wire rst;
	output wire [31:0] bus_out;
	output reg [7:0] inj_data_out_1755374690838_314;
	output wire [7:0] inj_field0_byte_o_1755374690832_197;
	reg [31:0] din;
	reg [31:0] dout;
	reg [15:0] my_union_var;
	always @(posedge clk)
		if (inj_en_1755374690838_231)
			inj_data_out_1755374690838_314 <= inj_data_in_1755374690838_411;
	always @(*) begin
		if (_sv2v_0)
			;
		my_union_var[15-:16] = inj_packed_in_1755374690832_418;
	end
	assign inj_field0_byte_o_1755374690832_197 = my_union_var[0+:8];
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
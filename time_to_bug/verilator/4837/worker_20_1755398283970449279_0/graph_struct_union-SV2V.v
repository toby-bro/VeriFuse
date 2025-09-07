module ConditionalOps (
	sel,
	val_false,
	val_true,
	out_val
);
	input wire sel;
	input wire signed [31:0] val_false;
	input wire signed [31:0] val_true;
	output wire signed [31:0] out_val;
	assign out_val = (sel ? val_true : val_false);
endmodule
module graph_struct_union (
	bus_in,
	clk,
	inj_data0_1755398284307_429,
	inj_data1_1755398284307_798,
	inj_sel_1755398284308_853,
	inj_val_false_1755398284317_911,
	inj_val_true_1755398284317_34,
	rst,
	bus_out,
	inj_data_out_1755398284308_185,
	inj_out_val_1755398284317_427
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [15:0] inj_data0_1755398284307_429;
	input wire [15:0] inj_data1_1755398284307_798;
	input wire inj_sel_1755398284308_853;
	input wire signed [31:0] inj_val_false_1755398284317_911;
	input wire signed [31:0] inj_val_true_1755398284317_34;
	input wire rst;
	output wire [31:0] bus_out;
	output reg [15:0] inj_data_out_1755398284308_185;
	output wire signed [31:0] inj_out_val_1755398284317_427;
	reg [31:0] din;
	reg [31:0] dout;
	ConditionalOps ConditionalOps_inst_1755398284317_8584(
		.val_true(inj_val_true_1755398284317_34),
		.out_val(inj_out_val_1755398284317_427),
		.sel(inj_sel_1755398284308_853),
		.val_false(inj_val_false_1755398284317_911)
	);
	always @(inj_sel_1755398284308_853 or inj_data0_1755398284307_429 or inj_data1_1755398284307_798)
		if (inj_sel_1755398284308_853)
			inj_data_out_1755398284308_185 = inj_data1_1755398284307_798;
		else
			inj_data_out_1755398284308_185 = inj_data0_1755398284307_429;
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
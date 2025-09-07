module graph_struct_union (
	bus_in,
	clk,
	inj_select_a_1755301683136_508,
	rst,
	bus_out,
	inj_out_val_1755301683136_193
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire inj_select_a_1755301683136_508;
	input wire rst;
	output wire [31:0] bus_out;
	output reg [31:0] inj_out_val_1755301683136_193;
	reg [31:0] din;
	reg [31:0] dout;
	reg [31:0] union_var;
	always @(*) begin
		if (_sv2v_0)
			;
		if (inj_select_a_1755301683136_508)
			union_var[31-:32] = bus_in;
		else
			union_var[31-:32] = bus_in[31:0];
		inj_out_val_1755301683136_193 = union_var[31-:32];
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
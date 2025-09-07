module more_procedural (
	p_in1,
	p_in2,
	p_mode,
	p_out
);
	reg _sv2v_0;
	input wire [31:0] p_in1;
	input wire [31:0] p_in2;
	input wire [1:0] p_mode;
	output reg [31:0] p_out;
	always @(*) begin
		if (_sv2v_0)
			;
		case (p_mode)
			2'b00: p_out = (p_in1 + p_in2) * 2;
			2'b01: p_out = (p_in1 - p_in2) / 3;
			2'b10: p_out = (p_in1 << 4) | (p_in2 >> 2);
			default: p_out = ~(p_in1 ^ p_in2) + 1;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module graph_struct_union (
	bus_in,
	clk,
	inj_p_in2_1755422089313_78,
	inj_p_mode_1755422089313_623,
	rst,
	bus_out,
	inj_p_out_1755422089313_217
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [31:0] inj_p_in2_1755422089313_78;
	input wire [1:0] inj_p_mode_1755422089313_623;
	input wire rst;
	output wire [31:0] bus_out;
	output wire [31:0] inj_p_out_1755422089313_217;
	reg [31:0] din;
	reg [31:0] dout;
	more_procedural more_procedural_inst_1755422089313_5603(
		.p_out(inj_p_out_1755422089313_217),
		.p_in1(bus_in),
		.p_in2(inj_p_in2_1755422089313_78),
		.p_mode(inj_p_mode_1755422089313_623)
	);
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
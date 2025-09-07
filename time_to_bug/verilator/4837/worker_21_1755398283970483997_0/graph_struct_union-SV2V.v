module ModuleBasic (
	a,
	b,
	out_a,
	out_b
);
	reg _sv2v_0;
	input wire a;
	input wire signed [31:0] b;
	output wire out_a;
	output wire signed [31:0] out_b;
	parameter signed [31:0] P1 = 10;
	localparam signed [31:0] LP1 = 20;
	reg c;
	wire signed [31:0] d;
	always @(*) begin : sv2v_autoblock_1
		reg temp_v;
		if (_sv2v_0)
			;
		temp_v = d;
		c = temp_v;
	end
	assign out_a = a;
	assign d = b;
	assign out_b = (d + P1) + LP1;
	initial _sv2v_0 = 0;
endmodule
module graph_struct_union (
	bus_in,
	clk,
	inj_data_in_1755398284286_350,
	inj_sel_in_1755398284286_669,
	rst,
	bus_out,
	inj_data_out_1755398284286_850
);
	reg _sv2v_0;
	parameter signed [31:0] SEL_PARAM = 6;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [3:0] inj_data_in_1755398284286_350;
	input wire signed [31:0] inj_sel_in_1755398284286_669;
	input wire rst;
	output wire [31:0] bus_out;
	output wire [7:0] inj_data_out_1755398284286_850;
	reg [31:0] din;
	reg [31:0] dout;
	ModuleBasic m1(
		.a(1'b1),
		.b(inj_sel_in_1755398284286_669),
		.out_a(),
		.out_b()
	);
	generate
		if (SEL_PARAM > 5) begin : gen_high
			wire signed [31:0] high_data_ts1755398284287;
			ModuleBasic m_high(
				.a(1'b0),
				.b(SEL_PARAM),
				.out_a(),
				.out_b(high_data_ts1755398284287)
			);
		end
		else begin : gen_low
			wire signed [31:0] low_data_ts1755398284287;
			ModuleBasic m_low(
				.a(1'b0),
				.b(SEL_PARAM),
				.out_a(),
				.out_b(low_data_ts1755398284287)
			);
		end
	endgenerate
	genvar _gv_i_1;
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	generate
		for (_gv_i_1 = 0; _gv_i_1 < 2; _gv_i_1 = _gv_i_1 + 1) begin : gen_loop
			localparam i = _gv_i_1;
			wire [1:0] sub_in_ts1755398284287;
			assign sub_in_ts1755398284287 = inj_data_in_1755398284286_350[i * 2+:2];
			wire signed [31:0] temp_int_ts1755398284287;
			ModuleBasic m_inst(
				.a(1'b0),
				.b(sv2v_cast_32_signed(sub_in_ts1755398284287)),
				.out_a(),
				.out_b(temp_int_ts1755398284287)
			);
			assign inj_data_out_1755398284286_850[i * 4+:4] = temp_int_ts1755398284287[3:0];
		end
	endgenerate
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
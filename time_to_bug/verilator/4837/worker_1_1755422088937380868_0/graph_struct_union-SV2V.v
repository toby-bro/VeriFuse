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
module generate_for_block (
	selector,
	selected_output
);
	reg _sv2v_0;
	input wire [1:0] selector;
	output reg [7:0] selected_output;
	wire [7:0] data [3:0];
	genvar _gv_i_1;
	function automatic signed [7:0] sv2v_cast_8_signed;
		input reg signed [7:0] inp;
		sv2v_cast_8_signed = inp;
	endfunction
	generate
		for (_gv_i_1 = 0; _gv_i_1 < 4; _gv_i_1 = _gv_i_1 + 1) begin : data_gen
			localparam i = _gv_i_1;
			assign data[i] = sv2v_cast_8_signed(i + 1) * sv2v_cast_8_signed(i + 1);
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		case (selector)
			0: selected_output = data[0];
			1: selected_output = data[1];
			2: selected_output = data[2];
			3: selected_output = data[3];
			default: selected_output = 8'hxx;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module graph_struct_union (
	bus_in,
	clk,
	inj_a_aa_1755422089406_652,
	inj_b_aa_1755422089406_621,
	inj_c_aa_1755422089406_957,
	inj_case_expr_1755422089276_377,
	inj_data_in_1755422089341_131,
	inj_sel_in_1755422089341_507,
	rst,
	bus_out,
	inj_data_out_1755422089341_324,
	inj_internal_out_1755422089276_245,
	inj_selected_output_1755422089350_251,
	inj_x_aa_1755422089406_54,
	inj_y_aa_1755422089406_310,
	inj_z_aa_1755422089406_235
);
	reg _sv2v_0;
	parameter signed [31:0] SEL_PARAM = 6;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [7:0] inj_a_aa_1755422089406_652;
	input wire [7:0] inj_b_aa_1755422089406_621;
	input wire [7:0] inj_c_aa_1755422089406_957;
	input wire [1:0] inj_case_expr_1755422089276_377;
	input wire [3:0] inj_data_in_1755422089341_131;
	input wire signed [31:0] inj_sel_in_1755422089341_507;
	input wire rst;
	output wire [31:0] bus_out;
	output wire [7:0] inj_data_out_1755422089341_324;
	output reg [4:0] inj_internal_out_1755422089276_245;
	output wire [7:0] inj_selected_output_1755422089350_251;
	output reg [7:0] inj_x_aa_1755422089406_54;
	output reg [7:0] inj_y_aa_1755422089406_310;
	output reg [7:0] inj_z_aa_1755422089406_235;
	reg [31:0] din;
	reg [31:0] dout;
	always @(*) begin
		inj_x_aa_1755422089406_54 = inj_a_aa_1755422089406_652 + inj_b_aa_1755422089406_621;
		inj_y_aa_1755422089406_310 = inj_x_aa_1755422089406_54 - inj_c_aa_1755422089406_957;
		inj_z_aa_1755422089406_235 = inj_a_aa_1755422089406_652 * inj_c_aa_1755422089406_957;
	end
	generate_for_block generate_for_block_inst_1755422089350_8878(
		.selector(inj_case_expr_1755422089276_377),
		.selected_output(inj_selected_output_1755422089350_251)
	);
	ModuleBasic m1(
		.a(1'b1),
		.b(inj_sel_in_1755422089341_507),
		.out_a(),
		.out_b()
	);
	generate
		if (SEL_PARAM > 5) begin : gen_high
			wire signed [31:0] high_data_ts1755422089341;
			ModuleBasic m_high(
				.a(1'b0),
				.b(SEL_PARAM),
				.out_a(),
				.out_b(high_data_ts1755422089341)
			);
		end
		else begin : gen_low
			wire signed [31:0] low_data_ts1755422089341;
			ModuleBasic m_low(
				.a(1'b0),
				.b(SEL_PARAM),
				.out_a(),
				.out_b(low_data_ts1755422089341)
			);
		end
	endgenerate
	genvar _gv_i_2;
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	generate
		for (_gv_i_2 = 0; _gv_i_2 < 2; _gv_i_2 = _gv_i_2 + 1) begin : gen_loop
			localparam i = _gv_i_2;
			wire [1:0] sub_in_ts1755422089341;
			assign sub_in_ts1755422089341 = inj_data_in_1755422089341_131[i * 2+:2];
			wire signed [31:0] temp_int_ts1755422089341;
			ModuleBasic m_inst(
				.a(1'b0),
				.b(sv2v_cast_32_signed(sub_in_ts1755422089341)),
				.out_a(),
				.out_b(temp_int_ts1755422089341)
			);
			assign inj_data_out_1755422089341_324[i * 4+:4] = temp_int_ts1755422089341[3:0];
		end
	endgenerate
	always @(*)
		(* full *)
		case (inj_case_expr_1755422089276_377)
			2'b00: inj_internal_out_1755422089276_245 = 10;
			2'b01: inj_internal_out_1755422089276_245 = 11;
			2'b10: inj_internal_out_1755422089276_245 = 12;
			default: inj_internal_out_1755422089276_245 = 13;
		endcase
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
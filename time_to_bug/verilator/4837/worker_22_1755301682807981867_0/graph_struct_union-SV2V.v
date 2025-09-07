module FunctionTaskMod (
	data_in,
	is_even
);
	input wire [7:0] data_in;
	output wire is_even;
	function automatic check_even;
		input reg [7:0] v;
		check_even = ~v[0];
	endfunction
	task automatic dummy_task;
		input reg [7:0] v;
		reg signed [31:0] tmp;
		tmp = v;
	endtask
	assign is_even = check_even(data_in);
endmodule
module graph_struct_union (
	bus_in,
	clk,
	inj_in1_1755301683136_381,
	inj_in2_1755301683136_197,
	inj_in_data_1755301683231_169,
	rst,
	bus_out,
	inj_is_even_1755301683175_628,
	inj_out1_1755301683136_398,
	inj_out2_1755301683136_95,
	inj_out_a_1755301683279_291,
	inj_out_data_pull0_1755301683231_603,
	inj_out_data_pull1_1755301683231_704,
	inj_out_h_1755301683381_485,
	inj_out_l_1755301683381_230
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [7:0] inj_in1_1755301683136_381;
	input wire [7:0] inj_in2_1755301683136_197;
	input wire inj_in_data_1755301683231_169;
	input wire rst;
	output wire [31:0] bus_out;
	output wire inj_is_even_1755301683175_628;
	output reg [7:0] inj_out1_1755301683136_398;
	output reg [7:0] inj_out2_1755301683136_95;
	output wire inj_out_a_1755301683279_291;
	output wire inj_out_data_pull0_1755301683231_603;
	output wire inj_out_data_pull1_1755301683231_704;
	output wire [3:0] inj_out_h_1755301683381_485;
	output wire [3:0] inj_out_l_1755301683381_230;
	reg [31:0] din;
	reg [31:0] dout;
	wire [7:0] internal_wire_ts1755301683136;
	wire conflict_var_ts1755301683279;
	parameter signed [31:0] conflict_param = 1;
	assign {inj_out_h_1755301683381_485, inj_out_l_1755301683381_230} = inj_in1_1755301683136_381;
	assign inj_out_a_1755301683279_291 = inj_in_data_1755301683231_169;
	assign inj_out_data_pull1_1755301683231_704 = inj_in_data_1755301683231_169;
	assign inj_out_data_pull0_1755301683231_603 = ~inj_in_data_1755301683231_169;
	FunctionTaskMod FunctionTaskMod_inst_1755301683175_133(
		.is_even(inj_is_even_1755301683175_628),
		.data_in(inj_in1_1755301683136_381)
	);
	assign internal_wire_ts1755301683136 = inj_in1_1755301683136_381 + inj_in2_1755301683136_197;
	always @(*) begin
		if (_sv2v_0)
			;
		if (internal_wire_ts1755301683136 > 8'd128)
			inj_out1_1755301683136_398 = internal_wire_ts1755301683136 - 1;
		else
			inj_out1_1755301683136_398 = internal_wire_ts1755301683136 + 1;
		inj_out2_1755301683136_95 = internal_wire_ts1755301683136 / 2;
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
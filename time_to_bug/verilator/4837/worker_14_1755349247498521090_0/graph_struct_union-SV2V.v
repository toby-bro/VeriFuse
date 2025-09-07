module Module_ControlFlow (
	clk,
	data_in,
	reset_n,
	sel_in,
	data_out
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] data_in;
	input wire reset_n;
	input wire [2:0] sel_in;
	output reg [7:0] data_out;
	reg [7:0] temp;
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (sel_in)
			3'b000: temp = data_in;
			3'b001: temp = data_in + 1;
			3'b010: temp = data_in - 1;
			default: temp = 8'haa;
		endcase
	end
	always @(posedge clk or negedge reset_n)
		if (!reset_n)
			data_out <= 8'h00;
		else
			data_out <= temp;
	initial _sv2v_0 = 0;
endmodule
module buf_primitive (
	i,
	o
);
	input wire i;
	output wire o;
	buf b1 (o, i);
endmodule
module comb_simple (
	in1,
	in2,
	out1,
	out2
);
	input wire [7:0] in1;
	input wire [7:0] in2;
	output reg [7:0] out1;
	output reg [7:0] out2;
	always @(*) begin
		out1 = in1 & in2;
		out2 = in1 | in2;
	end
endmodule
module mixed_conn_child (
	data_in,
	dummy_in,
	dummy_out
);
	reg _sv2v_0;
	input wire [7:0] data_in;
	input wire dummy_in;
	output wire dummy_out;
	reg dummy_internal;
	always @(*) begin
		if (_sv2v_0)
			;
		dummy_internal = |data_in | dummy_in;
	end
	assign dummy_out = dummy_internal;
	initial _sv2v_0 = 0;
endmodule
module split_if_empty_then (
	clk_p,
	condition_p,
	in_val_p,
	out_reg_p
);
	input wire clk_p;
	input wire condition_p;
	input wire [7:0] in_val_p;
	output reg [7:0] out_reg_p;
	always @(posedge clk_p)
		if (condition_p)
			;
		else
			out_reg_p <= in_val_p;
endmodule
module graph_struct_union (
	bus_in,
	clk,
	inj_addr_1755349247946_317,
	inj_condition_p_1755349247876_821,
	inj_data_in_1755349247855_714,
	inj_in1_1755349247823_835,
	inj_in2_1755349247823_350,
	inj_in2_1755349248078_519,
	inj_in_a_1755349248068_320,
	inj_in_b_1755349248068_169,
	inj_in_c_1755349248068_465,
	inj_sel_in_1755349247855_410,
	rst,
	bus_out,
	inj_data_out_1755349247855_54,
	inj_dummy_out_1755349247944_138,
	inj_o_1755349247825_716,
	inj_out1_1755349247823_724,
	inj_out1_1755349248078_931,
	inj_out2_1755349247823_802,
	inj_out2_1755349248078_476,
	inj_out_concat_1755349248068_868,
	inj_out_if_else_1755349248068_266,
	inj_out_reg_p_1755349247876_258,
	inj_write_status_1755349247946_95
);
	reg _sv2v_0;
	input wire [31:0] bus_in;
	input wire clk;
	input wire [7:0] inj_addr_1755349247946_317;
	input wire inj_condition_p_1755349247876_821;
	input wire [7:0] inj_data_in_1755349247855_714;
	input wire [7:0] inj_in1_1755349247823_835;
	input wire [7:0] inj_in2_1755349247823_350;
	input wire [7:0] inj_in2_1755349248078_519;
	input wire [3:0] inj_in_a_1755349248068_320;
	input wire [3:0] inj_in_b_1755349248068_169;
	input wire [7:0] inj_in_c_1755349248068_465;
	input wire [2:0] inj_sel_in_1755349247855_410;
	input wire rst;
	output wire [31:0] bus_out;
	output reg [7:0] inj_data_out_1755349247855_54;
	output wire inj_dummy_out_1755349247944_138;
	output wire inj_o_1755349247825_716;
	output wire [7:0] inj_out1_1755349247823_724;
	output wire [7:0] inj_out1_1755349248078_931;
	output wire [7:0] inj_out2_1755349247823_802;
	output wire [7:0] inj_out2_1755349248078_476;
	output reg [15:0] inj_out_concat_1755349248068_868;
	output reg [7:0] inj_out_if_else_1755349248068_266;
	output wire [7:0] inj_out_reg_p_1755349247876_258;
	output reg inj_write_status_1755349247946_95;
	reg [31:0] din;
	reg [31:0] dout;
	reg [7:0] intermediate1_ts1755349248078;
	reg [7:0] intermediate2_ts1755349248078;
	always @(*) intermediate1_ts1755349248078 = inj_in_c_1755349248068_465 & inj_in2_1755349248078_519;
	always @(*) intermediate2_ts1755349248078 = inj_in_c_1755349248068_465 | inj_in2_1755349248078_519;
	assign inj_out1_1755349248078_931 = intermediate1_ts1755349248078 + 8'd1;
	assign inj_out2_1755349248078_476 = intermediate2_ts1755349248078 - 8'd1;
	always @(*) begin
		if (_sv2v_0)
			;
		inj_out_concat_1755349248068_868 = {inj_in_a_1755349248068_320, inj_in_b_1755349248068_169, inj_in_c_1755349248068_465};
		if (rst)
			inj_out_if_else_1755349248068_266 = inj_in_c_1755349248068_465;
		else
			inj_out_if_else_1755349248068_266 = {inj_in_a_1755349248068_320, inj_in_b_1755349248068_169};
	end
	generate
		if (1) begin : vif_bus
			reg [7:0] data;
			reg ready;
			reg valid;
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		vif_bus.data = inj_data_in_1755349247855_714;
		vif_bus.ready = 1'b1;
		vif_bus.valid = 1'b0;
		inj_write_status_1755349247946_95 = vif_bus.ready;
	end
	mixed_conn_child mixed_conn_child_inst_1755349247944_4138(
		.dummy_in(inj_condition_p_1755349247876_821),
		.dummy_out(inj_dummy_out_1755349247944_138),
		.data_in(inj_data_in_1755349247855_714)
	);
	split_if_empty_then split_if_empty_then_inst_1755349247876_7179(
		.clk_p(clk),
		.condition_p(inj_condition_p_1755349247876_821),
		.in_val_p(inj_data_in_1755349247855_714),
		.out_reg_p(inj_out_reg_p_1755349247876_258)
	);
	wire [8:1] sv2v_tmp_Module_ControlFlow_inst_1755349247855_9896_data_out;
	always @(*) inj_data_out_1755349247855_54 = sv2v_tmp_Module_ControlFlow_inst_1755349247855_9896_data_out;
	Module_ControlFlow Module_ControlFlow_inst_1755349247855_9896(
		.clk(clk),
		.data_in(inj_data_in_1755349247855_714),
		.reset_n(rst),
		.sel_in(inj_sel_in_1755349247855_410),
		.data_out(sv2v_tmp_Module_ControlFlow_inst_1755349247855_9896_data_out)
	);
	buf_primitive buf_primitive_inst_1755349247825_9963(
		.i(clk),
		.o(inj_o_1755349247825_716)
	);
	comb_simple comb_simple_inst_1755349247823_4440(
		.in2(inj_in2_1755349247823_350),
		.out1(inj_out1_1755349247823_724),
		.out2(inj_out2_1755349247823_802),
		.in1(inj_in1_1755349247823_835)
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
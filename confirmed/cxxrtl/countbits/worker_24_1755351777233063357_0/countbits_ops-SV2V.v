module mod_if_elseif_chained (
	in_value,
	out_category
);
	reg _sv2v_0;
	input wire [7:0] in_value;
	output reg [2:0] out_category;
	always @(*) begin
		if (_sv2v_0)
			;
		if (in_value < 10)
			out_category = 3'd0;
		else if (in_value < 50)
			out_category = 3'd1;
		else if (in_value < 100)
			out_category = 3'd2;
		else
			out_category = 3'd3;
	end
	initial _sv2v_0 = 0;
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_data_case_b_1755351777634_656,
	inj_in_value_1755351777633_372,
	inj_select_case_1755351777634_128,
	rst,
	cnt,
	inj_case_output_ready_1755351777634_844,
	inj_out_category_1755351777633_459
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] in_d;
	input wire [7:0] inj_data_case_b_1755351777634_656;
	input wire [7:0] inj_in_value_1755351777633_372;
	input wire [1:0] inj_select_case_1755351777634_128;
	input wire rst;
	output wire [3:0] cnt;
	output reg inj_case_output_ready_1755351777634_844;
	output wire [2:0] inj_out_category_1755351777633_459;
	generate
		if (1) begin : case_vif_inst
			reg [7:0] data;
			reg ready;
			reg valid;
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		case (inj_select_case_1755351777634_128)
			2'b00: begin
				case_vif_inst.data = 8'haa;
				case_vif_inst.valid = 1'b1;
				case_vif_inst.ready = 1'b0;
			end
			2'b01: begin
				case_vif_inst.data = in_d;
				case_vif_inst.valid = 1'b0;
				case_vif_inst.ready = 1'b1;
			end
			2'b10: begin
				case_vif_inst.data = inj_data_case_b_1755351777634_656;
				case_vif_inst.valid = 1'b1;
				case_vif_inst.ready = 1'b1;
			end
			default: begin
				case_vif_inst.data = 8'hff;
				case_vif_inst.valid = 1'b0;
				case_vif_inst.ready = 1'b0;
			end
		endcase
		inj_case_output_ready_1755351777634_844 = case_vif_inst.ready;
	end
	mod_if_elseif_chained mod_if_elseif_chained_inst_1755351777633_2273(
		.out_category(inj_out_category_1755351777633_459),
		.in_value(inj_in_value_1755351777633_372)
	);
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
module mod_automatic_task (
	i_val,
	o_val
);
	reg _sv2v_0;
	input wire signed [31:0] i_val;
	output reg signed [31:0] o_val;
	task automatic update_val;
		input reg signed [31:0] in_v;
		output reg signed [31:0] out_v;
		out_v = in_v * 2;
	endtask
	always @(*) begin : sv2v_autoblock_1
		reg signed [31:0] temp_val;
		if (_sv2v_0)
			;
		update_val(i_val, temp_val);
		o_val = temp_val;
	end
	initial _sv2v_0 = 0;
endmodule
module countbits_ops (
	clk,
	in_d,
	inj_i_val_1755377830519_7,
	inj_in_1755377830518_867,
	rst,
	cnt,
	inj_o_val_1755377830519_747,
	inj_out1_1755377830518_880,
	inj_out2_1755377830518_117
);
	input wire clk;
	input wire [7:0] in_d;
	input wire signed [31:0] inj_i_val_1755377830519_7;
	input wire [31:0] inj_in_1755377830518_867;
	input wire rst;
	output wire [3:0] cnt;
	output wire signed [31:0] inj_o_val_1755377830519_747;
	output wire [7:0] inj_out1_1755377830518_880;
	output wire inj_out2_1755377830518_117;
	mod_automatic_task mod_automatic_task_inst_1755377830519_6757(
		.i_val(inj_i_val_1755377830519_7),
		.o_val(inj_o_val_1755377830519_747)
	);
	assign inj_out1_1755377830518_880 = inj_in_1755377830518_867[15:8];
	assign inj_out2_1755377830518_117 = inj_in_1755377830518_867[3];
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule
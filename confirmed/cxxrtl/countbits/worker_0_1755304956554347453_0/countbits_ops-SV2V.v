module countbits_ops (
	clk,
	in_d,
	inj_data0_1755304956858_225,
	inj_data1_1755304956858_180,
	inj_data_in_1755304956867_809,
	inj_in_val_1755304956862_68,
	inj_sel_1755304956858_762,
	rst,
	cnt,
	inj_control_status_1755304956867_645,
	inj_out_data_q_1755304956848_467,
	inj_out_val_1755304956862_657,
	inj_result_1755304956858_997
);
	reg _sv2v_0;
	input wire clk;
	input wire [7:0] in_d;
	input wire inj_data0_1755304956858_225;
	input wire inj_data1_1755304956858_180;
	input wire [15:0] inj_data_in_1755304956867_809;
	input wire signed [31:0] inj_in_val_1755304956862_68;
	input wire inj_sel_1755304956858_762;
	input wire rst;
	output wire [3:0] cnt;
	output reg inj_control_status_1755304956867_645;
	output wire inj_out_data_q_1755304956848_467;
	output wire signed [31:0] inj_out_val_1755304956862_657;
	output wire inj_result_1755304956858_997;
	generate
		if (1) begin : vif_inst
			reg [7:0] data;
			wire ready;
			wire valid;
		end
	endgenerate
	reg [7:0] data_q_ts1755304956849;
	generate
		if (1) begin : cif_inst
			reg [15:0] control_reg;
			wire [15:0] status_reg;
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		if (inj_data0_1755304956858_225)
			cif_inst.control_reg = inj_data_in_1755304956867_809;
		else
			cif_inst.control_reg = 16'h0000;
		inj_control_status_1755304956867_645 = cif_inst.control_reg != 16'h0000;
	end
	assign inj_out_val_1755304956862_657 = inj_in_val_1755304956862_68;
	assign inj_result_1755304956858_997 = (inj_sel_1755304956858_762 ? inj_data1_1755304956858_180 : inj_data0_1755304956858_225);
	always @(posedge clk or posedge rst)
		if (rst) begin
			vif_inst.data <= 8'h00;
			data_q_ts1755304956849 <= 8'h00;
		end
		else begin
			vif_inst.data <= in_d;
			data_q_ts1755304956849 <= vif_inst.data;
		end
	assign inj_out_data_q_1755304956848_467 = data_q_ts1755304956849;
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
	initial _sv2v_0 = 0;
endmodule
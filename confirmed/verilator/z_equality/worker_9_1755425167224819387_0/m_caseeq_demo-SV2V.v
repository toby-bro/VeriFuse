module m_caseeq_demo (
	clk,
	in,
	inj_i_target_data_1755425167519_276,
	rst,
	eq,
	inj_o_target_result_1755425167519_359,
	neq
);
	reg _sv2v_0;
	input wire clk;
	input wire in;
	input wire [7:0] inj_i_target_data_1755425167519_276;
	input wire rst;
	output wire eq;
	output reg [7:0] inj_o_target_result_1755425167519_359;
	output wire neq;
	reg tri_sig = 1'bz;
	always @(*) begin
		if (_sv2v_0)
			;
		inj_o_target_result_1755425167519_359 = inj_i_target_data_1755425167519_276 + 1;
	end
	assign eq = in === tri_sig;
	assign neq = in !== tri_sig;
	initial _sv2v_0 = 0;
endmodule
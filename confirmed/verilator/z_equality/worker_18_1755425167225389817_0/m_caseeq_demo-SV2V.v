module m_caseeq_demo (
	clk,
	in,
	inj_large_data_in_1755425167553_111,
	rst,
	eq,
	inj_large_sum_out_1755425167553_885,
	neq
);
	reg _sv2v_0;
	input wire clk;
	input wire in;
	input wire [1:0] inj_large_data_in_1755425167553_111;
	input wire rst;
	output wire eq;
	output reg [7:0] inj_large_sum_out_1755425167553_885;
	output wire neq;
	reg tri_sig = 1'bz;
	reg [7:0] current_large_sum_ts1755425167553;
	always @(*) begin
		if (_sv2v_0)
			;
		current_large_sum_ts1755425167553 = 8'h00;
		begin : sv2v_autoblock_1
			reg signed [31:0] m;
			for (m = 0; m < 40; m = m + 1)
				begin
					current_large_sum_ts1755425167553 = current_large_sum_ts1755425167553 + inj_large_data_in_1755425167553_111[0];
					current_large_sum_ts1755425167553 = current_large_sum_ts1755425167553 + inj_large_data_in_1755425167553_111[1];
					current_large_sum_ts1755425167553 = current_large_sum_ts1755425167553 + 1;
				end
		end
		inj_large_sum_out_1755425167553_885 = current_large_sum_ts1755425167553;
	end
	assign eq = in === tri_sig;
	assign neq = in !== tri_sig;
	initial _sv2v_0 = 0;
endmodule
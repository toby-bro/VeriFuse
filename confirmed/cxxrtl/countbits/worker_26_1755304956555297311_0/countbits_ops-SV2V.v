module countbits_ops (
	clk,
	in_d,
	rst,
	cnt,
	inj_is_even_1755304956898_531
);
	input wire clk;
	input wire [7:0] in_d;
	input wire rst;
	output wire [3:0] cnt;
	output wire inj_is_even_1755304956898_531;
	function automatic check_even;
		input reg [7:0] v;
		check_even = ~v[0];
	endfunction
	task automatic dummy_task;
		input reg [7:0] v;
		reg signed [31:0] tmp_ts1755304956899;
		tmp_ts1755304956899 = v;
	endtask
	assign inj_is_even_1755304956898_531 = check_even(in_d);
	assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule
module specify_basic(input wire in_sig, output wire out_sig);
  specparam delay_val = 2;
  specify
    (in_sig => out_sig) = delay_val;
  endspecify
endmodule
module specify_edge(input wire clk, output wire q);
  reg state;
  assign q = state;
  always @(posedge clk) state <= ~state;
  specparam edge_delay = 3;
  specify
    (posedge clk => q) = edge_delay;
  endspecify
endmodule
module specify_conditional(input wire sel, input wire a, input wire b, output wire y);
  assign y = sel ? a : b;
  specify
    if (sel) (a => y) = 1;
    if (!sel) (b => y) = 2;
    ifnone (a => y) = 3;
  endspecify
endmodule
module specify_parallel(input wire [3:0] vec_in, output wire [3:0] vec_out);
  assign vec_out = vec_in;
  specparam full_delay = 4;
  specify
    (vec_in *> vec_out) = full_delay;
  endspecify
endmodule
module timing_check_example(
  input  wire clk,
  input  wire data,
  input  wire en,
  input  wire reset_n,
  output reg  notifier
);
  always @(posedge clk) notifier <= 1'b0;
  specify
    $setup(posedge data, posedge clk, 10, notifier);
    $hold(negedge data, negedge clk, 5, notifier);
    $recovery(posedge reset_n, posedge clk, 8, notifier);
    $removal(negedge reset_n, negedge clk, 7, notifier);
    $skew(posedge data, posedge clk, 12, notifier);
    $setuphold(posedge data, posedge clk, 6, 8, notifier, en, reset_n, data, clk);
    $recrem(posedge data, posedge clk, 9, 11, notifier, en, reset_n, data, clk);
    $period(posedge clk, 20, notifier);
    $width(posedge data, 5, 6, notifier);
    $nochange(posedge clk, data, 10, 20, notifier);
  endspecify
endmodule

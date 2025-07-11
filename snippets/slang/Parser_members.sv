timeunit 1ns;
timeprecision 1ps;
module BitwiseAssign(input  logic [3:0] in_a,
                     input  logic [3:0] in_b,
                     output logic [3:0] out_y);
    assign out_y = in_a ^ in_b;
endmodule
module GenerateIfParam #(parameter bit GEN = 1)
                        (input  logic sig_in,
                         output logic sig_out);
    generate
        if (GEN) begin : g_true
            assign sig_out = sig_in;
        end
        else begin : g_false
            assign sig_out = ~sig_in;
        end
    endgenerate
endmodule
module GenerateFor(input  logic [3:0] data_in,
                   output logic [3:0] data_out);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_loop
            assign data_out[i] = data_in[i];
        end
    endgenerate
endmodule
module ClassCounter(input  logic clk,
                    output logic [7:0] count_out);
    class Counter;
        int count;
        function void inc(); count++; endfunction
    endclass
    Counter c;
    always_ff @(posedge clk) begin
        if (c == null) c = new();
        c.inc();
        count_out <= c.count[7:0];
    end
endmodule
module FunctionTaskMod(input  logic [7:0] data_in,
                       output logic       is_even);
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp;
        tmp = v;
    endtask
    assign is_even = check_even(data_in);
endmodule
module Parameterized #(parameter int WIDTH = 8)
                      (input  logic [WIDTH-1:0] din,
                       output logic [WIDTH-1:0] dout);
    assign dout = din;
endmodule
module ContinuousWire(input  logic din,
                      output wire  dout);
    wire internal_w;
    assign internal_w = din;
    assign dout       = internal_w;
endmodule
module AlwaysCombInvert(input  logic [3:0] a,
                        output logic [3:0] y);
    always_comb y = ~a;
endmodule

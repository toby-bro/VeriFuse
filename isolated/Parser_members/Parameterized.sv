module Parameterized #(
    parameter int WIDTH = 8
) (
    input logic [7:0] din,
    output logic [7:0] dout
);
    assign dout = din;
endmodule


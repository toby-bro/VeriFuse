module base_adder (
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] sum
);
    assign sum = a + b;
endmodule

module base_multiplier (
    input logic [7:0] x,
    input logic [7:0] y,
    output logic [15:0] product
);
    assign product = x * y;
endmodule

module complex_math (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [7:0] in_c,
    output logic [15:0] result
);
    logic [7:0] sum_out;
  
    // This module instantiation should be detected as a dependency
    base_adder adder_inst (
        .a(in_a),
        .b(in_b),
        .sum(sum_out)
    );
  
    // This module instantiation should also be detected as a dependency
    base_multiplier mult_inst (
        .x(sum_out),
        .y(in_c),
        .product(result)
    );
endmodule

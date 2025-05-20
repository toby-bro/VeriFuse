module wide_ops_deep (
    input logic [63:0] wide_b,
    input logic [63:0] wide_c,
    output logic [63:0] wide_out,
    input logic [63:0] wide_a
);
    assign wide_out = (((wide_a + wide_b) ^ wide_c) & (~wide_a | wide_b)) + (wide_c >>> 5);
endmodule


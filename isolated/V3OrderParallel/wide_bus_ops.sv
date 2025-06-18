module wide_bus_ops (
    input wire [63:0] wide_a,
    input wire [63:0] wide_b,
    output wire [127:0] concat_out,
    output wire [7:0] reduce_xor_out,
    output wire [63:0] wide_sum
);
    assign wide_sum = wide_a + wide_b;
    assign reduce_xor_out = ^wide_a[63:0];
    assign concat_out = {wide_a, wide_b};
endmodule


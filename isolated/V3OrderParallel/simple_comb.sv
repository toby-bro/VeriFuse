module simple_comb (
    input wire [7:0] in_data,
    output wire [7:0] out_data
);
    wire [7:0] intermediate_a;
    wire [7:0] intermediate_b;
    wire [7:0] intermediate_c;
    assign intermediate_a = in_data + 8'd1;
    assign intermediate_b = intermediate_a << 1;
    assign intermediate_c = intermediate_a >> 1;
    assign out_data = intermediate_b | intermediate_c;
endmodule


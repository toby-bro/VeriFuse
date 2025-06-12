module part_select_ops (
    output wire [7:0] upper_byte_out,
    output wire [7:0] lower_byte_out,
    input wire [31:0] wide_in
);
    wire [31:0] processed_wide;
    assign processed_wide = wide_in * 2;
    assign upper_byte_out = processed_wide[31:24];
    assign lower_byte_out = processed_wide[7:0];
endmodule


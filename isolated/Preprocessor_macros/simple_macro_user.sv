module simple_macro_user (
    input logic in1,
    output logic [31:0] out1
);
    `define SIMPLE_VALUE 32'd12345
    `define ANOTHER_SIMPLE (1 + 2)
    assign out1 = in1 ? (`SIMPLE_VALUE + `ANOTHER_SIMPLE) : 32'd0;
endmodule


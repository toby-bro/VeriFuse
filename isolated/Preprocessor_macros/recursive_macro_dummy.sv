module recursive_macro_dummy (
    input logic in_bit,
    output logic out_bit
);
    `define RECURSIVE_TEST `RECURSIVE_TEST
    assign out_bit = in_bit;
endmodule


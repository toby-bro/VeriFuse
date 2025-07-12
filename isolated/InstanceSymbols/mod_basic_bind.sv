module mod_basic_bind (
    input logic in1_bind_def,
    output logic out1_bind_def
);
    assign out1_bind_def = ~in1_bind_def;
endmodule


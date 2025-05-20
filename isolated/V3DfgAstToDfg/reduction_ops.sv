module reduction_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic out
);
    assign out = &in1 | ^in2;
endmodule


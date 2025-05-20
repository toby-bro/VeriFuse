module reduction_ops (
    output logic out,
    input logic [7:0] in1,
    input logic [7:0] in2
);
    assign out = &in1 | ^in2;
endmodule


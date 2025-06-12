module reduction_ops (
    input logic [7:0] in2,
    output logic out,
    input logic [7:0] in1
);
    assign out = &in1 | ^in2;
endmodule


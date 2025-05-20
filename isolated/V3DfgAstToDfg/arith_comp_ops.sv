module arith_comp_ops (
    input logic [15:0] in5,
    output logic out,
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [15:0] in3,
    input logic [15:0] in4
);
    assign out = (in1 + in2) * in3 > in4 - in5;
endmodule


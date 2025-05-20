module bitwise_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic [7:0] out
);
    assign out = (in1 & in2) | (~in3) ^ (in1 << 2) >> 1;
endmodule


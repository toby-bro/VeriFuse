module more_ops (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic anded,
    output logic diff,
    output logic ored,
    output logic [7:0] sum,
    output logic xored
);
    assign sum = a + b;
    assign diff = a > c;
    assign anded = a & b;
    assign ored = a | c;
    assign xored = a ^ b;
endmodule


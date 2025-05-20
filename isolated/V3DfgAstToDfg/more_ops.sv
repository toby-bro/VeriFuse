module more_ops (
    output logic [7:0] sum,
    output logic diff,
    output logic anded,
    output logic ored,
    output logic xored,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c
);
    assign sum = a + b;
    assign diff = a > c;
    assign anded = a & b;
    assign ored = a | c;
    assign xored = a ^ b;
endmodule


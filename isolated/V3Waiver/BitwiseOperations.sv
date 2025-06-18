module BitwiseOperations (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic [7:0] result_and,
    output logic [7:0] result_or,
    output logic [7:0] result_xor
);
    assign result_and = a & b;
    assign result_or = a | c;
    assign result_xor = b ^ c;
endmodule


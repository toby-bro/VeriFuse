module deep_logic (
    input logic [7:0] c,
    output logic [7:0] out,
    input logic [7:0] a,
    input logic [7:0] b
);
    assign out = (((a & b) | (~c)) ^ (a + b)) - (c << 2);
endmodule


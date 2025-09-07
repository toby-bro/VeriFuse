module countbits_ops (
    input logic [7:0] in_d,
    output logic [3:0] cnt
);
    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule


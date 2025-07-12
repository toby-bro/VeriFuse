module BitwiseAssign (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    output logic [3:0] out_y
);
    assign out_y = in_a ^ in_b;
endmodule


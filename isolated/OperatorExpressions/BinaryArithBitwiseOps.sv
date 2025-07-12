module BinaryArithBitwiseOps (
    input logic [15:0] a,
    input logic [15:0] b,
    input real r_a,
    input real r_b,
    output logic [15:0] out_add,
    output logic [15:0] out_band,
    output logic [15:0] out_bor,
    output logic [15:0] out_bxor,
    output logic [15:0] out_div,
    output logic out_gt,
    output logic [15:0] out_mul,
    output real out_radd,
    output real out_rmul,
    output logic [15:0] out_sub
);
    assign out_add  = a + b;
    assign out_sub  = a - b;
    assign out_mul  = a * b;
    assign out_div  = b == 0 ? 16'd0 : a / b;
    assign out_band = a & b;
    assign out_bor  = a | b;
    assign out_bxor = a ^ b;
    assign out_radd = r_a + r_b;
    assign out_rmul = r_a * r_b;
    assign out_gt   = a > b;
endmodule


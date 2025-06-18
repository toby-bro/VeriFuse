module split_arith_blocking (
    input logic [7:0] op1_u,
    input logic [7:0] op2_u,
    output logic [7:0] diff_u,
    output logic [7:0] prod_u,
    output logic [7:0] sum_u
);
    always @(*) begin
        sum_u = op1_u + op2_u;
        diff_u = op1_u - op2_u;
        prod_u = op1_u * op2_u;
    end
endmodule


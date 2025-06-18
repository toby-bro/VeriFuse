module split_arith_nb (
    input logic clk_v,
    input logic [7:0] op1_v,
    input logic [7:0] op2_v,
    output logic [7:0] diff_v,
    output logic [7:0] prod_v,
    output logic [7:0] sum_v
);
    always @(posedge clk_v) begin
        sum_v <= op1_v + op2_v;
        diff_v <= op1_v - op2_v;
        prod_v <= op1_v * op2_v;
    end
endmodule


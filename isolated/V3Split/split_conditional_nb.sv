module split_conditional_nb (
    input logic clk_d,
    input logic condition_d,
    input logic [7:0] in_false_d,
    input logic [7:0] in_true_d,
    output logic [7:0] out_reg_d
);
    always @(posedge clk_d) begin
        if (condition_d) begin
            out_reg_d <= in_true_d;
        end else begin
            out_reg_d <= in_false_d;
        end
    end
endmodule


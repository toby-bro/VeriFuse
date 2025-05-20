module split_if_empty_branches (
    input logic clk_t,
    input logic condition_t,
    input logic [7:0] in_val_t,
    output logic [7:0] out_reg_t
);
    always @(posedge clk_t) begin
        if (condition_t) begin
        end else begin
        end
    end
endmodule


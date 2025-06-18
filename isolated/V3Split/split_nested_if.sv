module split_nested_if (
    input logic clk_m,
    input logic cond1_m,
    input logic cond2_m,
    input logic [7:0] val_a_m,
    input logic [7:0] val_b_m,
    input logic [7:0] val_c_m,
    output logic [7:0] result_m
);
    always @(posedge clk_m) begin
        if (cond1_m) begin
            if (cond2_m) begin
                result_m <= val_a_m;
            end else begin
                result_m <= val_b_m;
            end
        end else begin
            result_m <= val_c_m;
        end
    end
endmodule


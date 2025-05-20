module split_for_loop (
    input logic [7:0] start_val_i,
    output logic [15:0] sum_out_i,
    input logic clk_i
);
    always @(posedge clk_i) begin
        sum_out_i <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            sum_out_i <= sum_out_i + start_val_i + i;
        end
    end
endmodule


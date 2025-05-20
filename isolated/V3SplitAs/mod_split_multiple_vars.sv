module mod_split_multiple_vars (
    output logic [7:0] out_mv_a,
    output logic [7:0] out_mv_b,
    output logic [7:0] out_mv_c,
    input logic clk,
    input logic reset,
    input logic [7:0] data_in
);
    logic [7:0]  split_mv_var;
    logic [7:0] other_mv_var1;
    logic [7:0] other_mv_var2;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_mv_var <= 8'b0;
            other_mv_var1 <= 8'b0;
            other_mv_var2 <= 8'b0;
        end else begin
            split_mv_var <= data_in;
            other_mv_var1 <= data_in + 1;
            other_mv_var2 <= data_in + 2;
            if (data_in > 100) begin
                split_mv_var <= 8'hFF;
            end
            out_mv_a <= split_mv_var;
            out_mv_b <= other_mv_var1;
            out_mv_c <= other_mv_var2;
        end
    end
endmodule


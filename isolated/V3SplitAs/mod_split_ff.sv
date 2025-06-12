module mod_split_ff (
    input logic [7:0] data_in,
    output logic [7:0] out_reg_a,
    output logic [7:0] out_reg_b,
    input logic clk,
    input logic reset
);
    logic [7:0]  split_reg_var;
    logic [7:0] other_reg_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_reg_var <= 8'b0;
            other_reg_var <= 8'b0;
            out_reg_a <= 8'b0;
            out_reg_b <= 8'b0;
        end else begin
            split_reg_var <= data_in;
            other_reg_var <= data_in + 2;
            out_reg_a <= split_reg_var;
            out_reg_b <= other_reg_var;
        end
    end
endmodule


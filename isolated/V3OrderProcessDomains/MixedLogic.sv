module MixedLogic (
    input logic async_reset,
    input logic clk,
    input logic comb_in1,
    input logic comb_in2,
    input logic seq_in,
    output logic comb_out,
    output logic seq_out
);
    logic seq_reg;
    logic comb_intermediate;
    always @(posedge clk or negedge async_reset) begin
        if (!async_reset) begin
            seq_reg <= 1'b0;
        end else begin
            seq_reg <= seq_in;
        end
    end
    assign seq_out = seq_reg;
    always @(seq_reg or comb_in1 or comb_in2) begin
        comb_intermediate = (seq_reg & comb_in1) | (~seq_reg & comb_in2);
    end
    assign comb_out = comb_intermediate;
endmodule


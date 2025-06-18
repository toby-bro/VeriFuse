module ModMultipleAlways (
    input logic clk_a,
    input logic clk_b,
    input logic din_a,
    input logic din_b,
    input logic rst_n,
    output logic dout_a,
    output logic dout_b
);
    always @(posedge clk_a or negedge rst_n) begin 
    if (!rst_n) begin 
        dout_a <= 1'b0;
    end else begin
        dout_a <= din_a; 
    end
    end
    always @(posedge clk_b) begin 
    dout_b <= din_b; 
    end
endmodule


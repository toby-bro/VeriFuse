module ModClockedWithSimpleAssign (
    input logic in_b,
    output logic out_comb,
    output logic out_reg,
    input logic clk,
    input logic in_a
);
    logic internal_reg;
    always @(posedge clk) begin 
    internal_reg <= in_a; 
    end
    assign out_comb = in_a ^ in_b; 
    always @(posedge clk) begin 
    out_reg <= internal_reg & in_b; 
    end
endmodule


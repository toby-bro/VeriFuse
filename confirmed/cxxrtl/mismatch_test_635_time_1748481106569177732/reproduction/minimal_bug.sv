module bug;
    reg [6:0] reg_bug;
    reg clk = 1;
    
    always_ff @(negedge clk)
        reg_bug <= 7'b0011111;
    
    initial #1 clk = 0;
    
    always_comb assert(reg_bug == 7'b0011111);
endmodule

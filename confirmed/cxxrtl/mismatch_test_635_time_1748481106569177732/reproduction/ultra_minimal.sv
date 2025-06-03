// Ultra-minimal CXXRTL negedge bug - just the core issue
module bug;
    // Hardcoded values from test case 635
    wire reset = 1'b0;  // No reset (bit 32 of clkin_data = 0)
    wire [6:0] expected_data = 7'b0011111;  // Expected register value
    
    reg [6:0] reg_bug;
    reg clk = 1;
    
    // THE BUG: negedge register fails to update in CXXRTL
    always_ff @(negedge clk, posedge reset)
        if (reset)
            reg_bug <= 7'h00;
        else 
            reg_bug <= expected_data;
    
    initial begin
        #1 clk = 0;  // negedge trigger
        #1 $display("reg_bug=%b expected=0011111 %s", 
                   reg_bug, reg_bug == 7'b0011111 ? "✓" : "✗");
    end
endmodule

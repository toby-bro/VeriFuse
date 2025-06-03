// Test with proper clock driving
module bug_cleaner;
    wire reset = 1'b0;
    wire [6:0] expected_data = 7'b0011111;
    
    reg [6:0] reg_bug;
    reg clk;
    
    // Proper clock generation
    initial begin
        clk = 1;
        #1 clk = 0;  // negedge
        #1 $display("reg_bug=%b expected=0011111 %s", 
                   reg_bug, reg_bug == 7'b0011111 ? "✓" : "✗");
    end
    
    // THE BUG: negedge register
    always_ff @(negedge clk, posedge reset)
        if (reset)
            reg_bug <= 7'h00;
        else 
            reg_bug <= expected_data;
endmodule

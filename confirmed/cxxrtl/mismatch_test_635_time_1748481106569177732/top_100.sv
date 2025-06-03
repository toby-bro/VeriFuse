// Ultra-minimal test case for CXXRTL negedge trigger bug
// Bug: Register with negedge trigger + async reset fails to update in CXXRTL

module topi (
    clkin_data,
    in_data,
    out_data,
    inj_param_out_547
);
    // *** THE PROBLEMATIC REGISTER - Core of the CXXRTL bug ***
    reg [6:0] _11_;
    
    // Simple clock signal that transitions 1->0 to trigger negedge
    reg simple_clock;
    
    // I/O ports (must preserve interface)
    input [95:0] clkin_data;
    input [191:0] in_data;
    output [191:0] out_data;
    output wire [7:0] inj_param_out_547;
    
    // Direct output from problematic register  
    assign inj_param_out_547 = {1'b0, _11_};
    assign out_data = 192'b0;
    
    // *** THE BUG: This negedge-triggered register with async reset ***
    // Works in Verilator: Updates on negedge when reset is low
    // Fails in CXXRTL: Stays stuck at reset value
    always_ff @(negedge simple_clock, posedge clkin_data[32])
        if (clkin_data[32]) 
            _11_ <= 7'h00;  // Async reset to 0
        else 
            _11_ <= { in_data[48:43], (| in_data[84:76]) };  // Should update to {001111, 1} = 0011111
    
    // Simple clock generation: Start at 1, then go to 0 to create negedge
    initial begin
        simple_clock = 1'b1;  // Start high
        #1;
        simple_clock = 1'b0;  // Go low -> creates negedge trigger
    end
    
    // Debug output
    initial begin
        $display("=== ULTRA-MINIMAL CXXRTL NEGEDGE BUG TEST ===");
        $display("Reset (clkin_data[32]): %b", clkin_data[32]);
        $display("Expected data: in_data[48:43]=%b, |in_data[84:76]=%b", 
                 in_data[48:43], (| in_data[84:76]));
        $display("Expected _11_ update: {%b, %b} = %b", 
                 in_data[48:43], (| in_data[84:76]), {in_data[48:43], (| in_data[84:76])});
        $display("Testing: always_ff @(negedge simple_clock, posedge reset)");
    end
    
    always @(_11_) begin
        $display("Time %0t: _11_ = %b (%s)", $time, _11_, 
                 (_11_ == 7'b0000000) ? "STUCK AT RESET" : "UPDATED CORRECTLY");
    end
    
    always @(simple_clock) begin
        $display("Time %0t: simple_clock = %b %s", $time, simple_clock,
                 simple_clock ? "" : "(negedge - should trigger _11_)");
    end
    
    always @(clkin_data[32]) begin
        $display("Time %0t: reset = %b", $time, clkin_data[32]);
    end
    
    // Final check
    always @(inj_param_out_547) begin
        $display("Time %0t: inj_param_out_547 = %b", $time, inj_param_out_547);
        if (inj_param_out_547 == 8'b00000000) begin
            $display(">>> CXXRTL BUG: Register stuck at reset value!");
        end else if (inj_param_out_547 == 8'b00011111) begin
            $display(">>> CORRECT: Register updated on negedge!");
        end
    end
endmodule

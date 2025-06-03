// MINIMAL TEST CASE for CXXRTL Bug: Register with negative edge trigger not updating
// Bug: _11_ register fails to update on negedge in CXXRTL but works correctly in Verilator
// Expected: When clock_signal goes from 1→0, register should update to new value
// Actual in CXXRTL: Register remains at reset value forever

module topi (
    clkin_data,
    in_data,
    out_data,
    inj_param_out_547
);
    // I/O ports (must be preserved)
    input [95:0] clkin_data;
    input [191:0] in_data;
    output [191:0] out_data;
    output wire [7:0] inj_param_out_547;
    
    // *** PROBLEMATIC REGISTER - Core of the bug ***
    reg [6:0] _11_;
    
    // Simple clock signal for minimal reproduction
    // This will transition from 0→1→0 during simulation to trigger negedge
    wire clock_signal;
    assign clock_signal = in_data[100] & ~in_data[50]; // Simple combination that creates the transition
    
    // *** THE BUG: This register updates correctly in Verilator but not in CXXRTL ***
    // Expected: Should update to in_data[48:42] when clock_signal goes 1→0 at time 5
    always_ff @(negedge clock_signal, posedge clkin_data[32])
        if (clkin_data[32]) 
            _11_ <= 7'h00;  // Reset to 0
        else 
            _11_ <= in_data[48:42];  // Should load this value on negedge
    
    // Direct path to output for observation
    assign inj_param_out_547 = {1'b0, _11_};  // Just pass through _11_ with padding
    
    // Minimal output assignment
    assign out_data = 192'b0;
    
    // === DEBUG MONITORING ===
    initial begin
        $display("=== MINIMAL CXXRTL NEGEDGE BUG TEST ===");
        $display("Time %0t: Simulation started", $time);
        $display("Target value for _11_: in_data[48:42] = %b", in_data[48:42]);
        $display("Reset signal: clkin_data[32] = %b", clkin_data[32]);
        $display("Clock signal: %b (should transition 0→1→0)", clock_signal);
        $display("Initial _11_ value: %b", _11_);
    end
    
    // Monitor the problematic register - this is where we see the bug
    always @(_11_) begin
        $display("Time %0t: *** _11_ register changed to %b (hex: 0x%h) ***", $time, _11_, _11_);
    end
    
    // Monitor the clock signal transitions
    always @(clock_signal) begin
        $display("Time %0t: clock_signal = %b", $time, clock_signal);
        if (clock_signal == 0 && $time > 0) begin
            $display("Time %0t: ↓ NEGATIVE EDGE detected - _11_ should update to %b", $time, in_data[48:42]);
        end
    end
    
    // Monitor reset
    always @(clkin_data[32]) begin
        $display("Time %0t: Reset clkin_data[32] = %b", $time, clkin_data[32]);
    end
    
    // Final result check
    always @(inj_param_out_547) begin
        $display("Time %0t: OUTPUT inj_param_out_547 = %b (hex: 0x%h)", $time, inj_param_out_547, inj_param_out_547);
    end
    
    // Detailed analysis at end of critical timing
    always @(posedge clkin_data[32]) begin
        #2; // Small delay to let everything settle
        if ($time > 5) begin
            $display("=== FINAL ANALYSIS at time %0t ===", $time);
            $display("clock_signal current value: %b", clock_signal);
            $display("_11_ register actual value: %b (0x%h)", _11_, _11_);
            $display("_11_ register expected value: %b (0x%h)", in_data[48:42], in_data[48:42]);
            $display("inj_param_out_547 output: %b (0x%h)", inj_param_out_547, inj_param_out_547);
            
            if (_11_ == in_data[48:42]) begin
                $display("✓ PASS: Register updated correctly on negedge");
            end else begin
                $display("✗ FAIL: Register did not update on negedge - CXXRTL BUG!");
                $display("  This register should have updated when clock_signal went 1→0");
                $display("  Verilator: Updates correctly");
                $display("  CXXRTL: Stays at reset value");
            end
            $display("================================");
        end
    end
endmodule

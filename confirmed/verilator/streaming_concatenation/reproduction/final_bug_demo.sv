// Final demonstration: Verilator bug in streaming concatenation
module test_streaming_bug;
    logic [7:0] b = 8'hA5;  // Test pattern: 10100101
    logic [31:0] y;
    
    // The problematic assignment
    always_comb begin
        y = {<<{b}};  // Should place result in MSBs, zeros in LSBs
    end
    
    initial begin
        #10;  // Let it settle
        
        $display("Input b = %h (%b)", b, b);
        $display("Output y = %h (%b)", y, y);
        $display("");
        $display("According to IEEE 1800-2023:");
        $display("  Stream should be in MSBs: %h", {b, 24'b0});
        $display("  Zeros should be in LSBs");
        $display("");
        $display("Verilator result: %h", y);
        $display("Expected result:  %h", {b, 24'b0});
        $display("");
        
        if (y == {b, 24'b0}) begin
            $display("✓ PASS: Verilator is correct");
        end else begin
            $display("✗ FAIL: Verilator bug - stream placed in LSBs instead of MSBs");
            $display("   Got: %h", y);
            $display("   Expected: %h", {b, 24'b0});
        end
        
        $finish;
    end
endmodule

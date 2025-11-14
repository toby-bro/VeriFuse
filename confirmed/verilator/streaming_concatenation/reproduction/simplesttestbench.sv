// Simplest testbench
module top;
    logic [7:0] in8;
    logic [31:0] out_stream_left;
    logic [31:0] out_stream_right;
    logic [15:0] out_stream_narrow;
    logic [63:0] out_stream_wide;
    logic [31:0] out_concat;
    logic [31:0] out_replicate;

    simplest dut (
        .in8(in8),
        .out_stream_left(out_stream_left),
        .out_stream_right(out_stream_right),
        .out_stream_narrow(out_stream_narrow),
        .out_stream_wide(out_stream_wide),
        .out_concat(out_concat),
        .out_replicate(out_replicate)
    );

    initial begin
        // Hardcode input
        in8 = 8'hA5;  // Test pattern: 10100101
        
        // Let signals settle
        #10;
        
        // Display results
        $display("Input: in8 = %h (%b)", in8, in8);
        $display("");
        $display("Streaming operators:");
        $display("  out_stream_left  (32-bit): %h (%b)", out_stream_left, out_stream_left);
        $display("  out_stream_right (32-bit): %h (%b)", out_stream_right, out_stream_right);
        $display("  out_stream_narrow(16-bit): %h (%b)", out_stream_narrow, out_stream_narrow);
        $display("  out_stream_wide  (64-bit): %h (%b)", out_stream_wide, out_stream_wide);
        $display("");
        $display("Regular operators (for comparison):");
        $display("  out_concat       (32-bit): %h (%b)", out_concat, out_concat);
        $display("  out_replicate    (32-bit): %h (%b)", out_replicate, out_replicate);
        
        $finish;
    end
endmodule

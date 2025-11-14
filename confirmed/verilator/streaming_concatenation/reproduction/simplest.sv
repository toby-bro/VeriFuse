// Simplest test case: streaming operators with different width targets
module simplest (
    input logic [7:0] in8,
    output logic [31:0] out_stream_left,
    output logic [31:0] out_stream_right,
    output logic [15:0] out_stream_narrow,
    output logic [63:0] out_stream_wide,
    output logic [31:0] out_concat,
    output logic [31:0] out_replicate
);
    // Test 1: Left streaming to wider target
    always_comb begin
        out_stream_left = {<<{in8}};
    end
    
    // Test 2: Right streaming to wider target
    always_comb begin
        out_stream_right = {>>{in8}};
    end
    
    // Test 3: Left streaming to narrower target (truncation)
    always_comb begin
        out_stream_narrow = {<<{in8}};
    end
    
    // Test 4: Left streaming to much wider target
    always_comb begin
        out_stream_wide = {<<{in8}};
    end
    
    // Test 5: Regular concatenation (for comparison)
    always_comb begin
        out_concat = {24'b0, in8};
    end
    
    // Test 6: Replication (for comparison)
    always_comb begin
        out_replicate = {4{in8}};
    end
endmodule

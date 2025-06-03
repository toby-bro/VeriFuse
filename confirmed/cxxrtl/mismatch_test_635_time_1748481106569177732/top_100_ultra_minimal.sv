// Minimal test case for CXXRTL negedge trigger bug
// Bug: Register with negedge trigger + async reset fails to update in CXXRTL

module topi (
    clkin_data,
    in_data,
    out_data,
    inj_param_out_547
);
    // *** THE PROBLEMATIC REGISTER - Core of the CXXRTL bug ***
    reg [6:0] _11_;
    
    // Clock signal that controls the negedge trigger
    wire celloutsig_1_19z;
    
    // Data signal for register update
    wire celloutsig_0_0z;
    
    // Supporting registers for clock generation
    reg [11:0] _01_;
    reg [4:0] _02_;
    
    // Supporting signals for clock generation
    wire celloutsig_1_0z;
    wire celloutsig_1_14z;
    wire celloutsig_1_12z;
    wire celloutsig_1_4z;
    wire [3:0] celloutsig_1_1z;
    wire [5:0] celloutsig_1_2z;
    wire celloutsig_1_3z;
    wire [11:0] celloutsig_1_9z;
    wire celloutsig_1_10z;
    
    // I/O ports
    input [95:0] clkin_data;
    input [191:0] in_data;
    output [191:0] out_data;
    output wire [7:0] inj_param_out_547;
    
    // Direct output from problematic register
    assign inj_param_out_547 = {1'b0, _11_};
    assign out_data = 192'b0;  // Simplified
    
    // *** THE BUG: This negedge-triggered register with async reset ***
    // Works in Verilator, fails in CXXRTL
    always_ff @(negedge celloutsig_1_19z, posedge clkin_data[32])
        if (clkin_data[32]) 
            _11_ <= 7'h00;  // Async reset
        else 
            _11_ <= { in_data[48:43], celloutsig_0_0z };  // Should update on negedge
    
    // Supporting registers for clock generation
    always_ff @(posedge clkin_data[0], posedge clkin_data[64])
        if (clkin_data[64]) 
            _01_ <= 12'h000;
        else 
            _01_ <= in_data[107:96];
    
    always_ff @(posedge clkin_data[0], negedge clkin_data[64])
        if (!clkin_data[64]) 
            _02_ <= 5'h00;
        else 
            _02_ <= { _01_[6:3], celloutsig_1_3z };
    
    // Clock generation logic (essential for reproducing the timing)
    assign celloutsig_1_0z = in_data[144] ^ in_data[107];
    assign celloutsig_1_1z = { in_data[168:167], celloutsig_1_0z, celloutsig_1_0z } / { 1'h1, in_data[126:124] };
    assign celloutsig_1_2z = { celloutsig_1_1z, celloutsig_1_0z, celloutsig_1_0z } <<< { in_data[97:96], celloutsig_1_1z };
    assign celloutsig_1_3z = { celloutsig_1_2z[2:0], celloutsig_1_0z } != in_data[174:171];
    assign celloutsig_1_4z = | { celloutsig_1_2z[5:3], celloutsig_1_0z };
    assign celloutsig_1_9z = { celloutsig_1_4z, celloutsig_1_1z, celloutsig_1_2z, celloutsig_1_0z } <<< in_data[130:119];
    assign celloutsig_1_10z = | { _01_[10:0], celloutsig_1_4z };
    assign celloutsig_1_12z = | { celloutsig_1_9z[11:8], celloutsig_1_4z, celloutsig_1_10z, _02_ };
    assign celloutsig_1_14z = celloutsig_1_12z ^ celloutsig_1_4z;
    
    // *** KEY: This is the clock signal that should trigger _11_ on negedge ***
    assign celloutsig_1_19z = _01_[11:8] === { in_data[168:166], celloutsig_1_14z };
    
    // Data for register update
    assign celloutsig_0_0z = | in_data[84:76];
    
    // Debug output
    initial begin
        $display("=== CXXRTL NEGEDGE TRIGGER BUG TEST ===");
        $display("Testing: always_ff @(negedge signal, posedge reset)");
        $display("Expected: Register should update on negedge when reset is low");
        $display("CXXRTL Bug: Register stays at reset value");
    end
    
    always @(_11_) begin
        $display("Time %0t: _11_ = %b", $time, _11_);
    end
    
    always @(celloutsig_1_19z) begin
        $display("Time %0t: celloutsig_1_19z = %b (negedge should trigger _11_)", $time, celloutsig_1_19z);
    end
    
    always @(clkin_data[32]) begin
        $display("Time %0t: reset = %b", $time, clkin_data[32]);
    end
endmodule

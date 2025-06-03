// Ultra-minimal test case focusing on the timing-dependent logic that causes the mismatch
module module_with_params #(
    parameter integer DATA_WIDTH = 8
) (
    input wire [7:0] param_in,
    output wire [7:0] param_out
);
    assign param_out = param_in;
endmodule

module topi (
    clkin_data,
    in_data,
    inj_param_out_547
);
    input [95:0] clkin_data;
    input [191:0] in_data;
    output wire [7:0] inj_param_out_547;
    
    // Essential registers and wires that affect celloutsig_0_8z
    reg [11:0] _01_;
    wire [6:0] _03_;
    wire _00_;
    wire celloutsig_0_0z;
    wire celloutsig_0_2z;
    wire celloutsig_0_3z;
    wire [7:0] celloutsig_0_8z;
    
    // Key timing-dependent logic
    always_ff @(posedge clkin_data[0], posedge clkin_data[64])
        if (clkin_data[64]) _01_ <= 12'h000;
        else _01_ <= in_data[107:96];
    
    reg [6:0] _11_;
    wire celloutsig_1_19z;
    assign celloutsig_1_19z = _01_[11:8] === in_data[168:166]; // Simplified comparison
    
    always_ff @(negedge celloutsig_1_19z, posedge clkin_data[32])
        if (clkin_data[32]) _11_ <= 7'h00;
        else _11_ <= in_data[48:42]; // Simplified
    
    assign { _03_[6:2], _00_, _03_[0] } = _11_;
    
    // Core logic that produces the mismatch
    assign celloutsig_0_0z = | in_data[84:76];
    assign celloutsig_0_2z = !(celloutsig_0_0z ? celloutsig_0_0z : in_data[47]);
    assign celloutsig_0_3z = | { _00_, celloutsig_0_2z, _03_[6:2], _03_[0], in_data[15:3] };
    
    // The critical assignment that shows different results
    assign celloutsig_0_8z = { 1'b0, _03_[6:2], _00_, _03_[0] } ~^ { _03_[5:2], _00_, _03_[0], celloutsig_0_3z, celloutsig_0_3z };
    
    // Connect to parameterized module
    module_with_params module_with_params_inst_1000 (
        .param_in(celloutsig_0_8z),
        .param_out(inj_param_out_547)
    );
    
    assign _03_[1] = _00_;
endmodule

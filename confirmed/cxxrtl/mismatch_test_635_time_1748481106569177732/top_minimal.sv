// Minimal test case to isolate the Verilator vs CXXRTL mismatch
module module_with_params #(
    parameter integer DATA_WIDTH = 8
) (
    input wire [7:0] param_in,
    output wire [7:0] param_out
);
    assign param_out = param_in;
endmodule

module topi (
    in_data,
    inj_param_out_547
);
    input [191:0] in_data;
    output wire [7:0] inj_param_out_547;
    
    // Minimal logic to reproduce the mismatch
    wire celloutsig_0_0z;
    wire celloutsig_0_2z;  
    wire celloutsig_0_3z;
    wire [7:0] celloutsig_0_8z;
    wire [6:0] _03_;
    wire _00_;
    
    // Key logic from original that affects celloutsig_0_8z
    assign celloutsig_0_0z = | in_data[84:76];
    assign celloutsig_0_2z = !(celloutsig_0_0z ? celloutsig_0_0z : in_data[47]);
    assign _03_ = in_data[48:42]; // Simplified - remove timing dependency
    assign _00_ = in_data[41];    // Simplified
    assign celloutsig_0_3z = | { _00_, celloutsig_0_2z, _03_, in_data[15:3] };
    
    // This is the key assignment that produces different results
    assign celloutsig_0_8z = { 1'b0, _03_[6:2], _00_, _03_[0] } ~^ { _03_[5:2], _00_, _03_[0], celloutsig_0_3z, celloutsig_0_3z };
    
    // Connect to parameterized module
    module_with_params module_with_params_inst_1000 (
        .param_in(celloutsig_0_8z),
        .param_out(inj_param_out_547)
    );
endmodule

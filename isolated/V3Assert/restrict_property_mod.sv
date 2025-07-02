module restrict_property_mod (
    input logic clk,
    input logic debug_mode,
    input logic reset_n,
    input logic restrict_cond,
    input logic test_mode,
    output logic restrict_out
);
    property p_restrict_debug_only;
        @(posedge clk) disable iff (!reset_n)
        1'b1 |-> debug_mode;
    endproperty
    restrict property (p_restrict_debug_only);
    property p_restrict_no_test_mode;
        @(posedge clk) disable iff (!reset_n)
        !test_mode;
    endproperty
    restrict property (p_restrict_no_test_mode);
    assign restrict_out = restrict_cond && debug_mode && !test_mode;
endmodule


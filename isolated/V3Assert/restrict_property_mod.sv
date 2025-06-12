module restrict_property_mod (
    output logic restrict_out,
    input logic clk,
    input logic restrict_cond
);
    property p_restrict_simple_concurrent;
        @(posedge clk) restrict_cond;
    endproperty
    restrict property (p_restrict_simple_concurrent);
    assign restrict_out = restrict_cond;
endmodule


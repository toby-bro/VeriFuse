module assume_property_mod (
    output logic assume_out,
    input logic clk,
    input logic assume_cond
);
    property p_assume_simple_concurrent;
        @(posedge clk) assume_cond;
    endproperty
    assume property (p_assume_simple_concurrent);
    always @(posedge clk) begin
        assume (assume_cond);
    end
    assign assume_out = assume_cond;
endmodule


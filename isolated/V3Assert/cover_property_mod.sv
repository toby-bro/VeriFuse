module cover_property_mod (
    input logic clk,
    input logic cover_cond,
    output logic cover_out
);
    property p_cover_simple_concurrent;
        @(posedge clk) cover_cond;
    endproperty
    cover property (p_cover_simple_concurrent);
    always @(posedge clk) begin
        cover (cover_cond);
    end
    assign cover_out = cover_cond;
endmodule


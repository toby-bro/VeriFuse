module ConditionalAndCasts (
    input logic condition,
    input logic [15:0] value_a,
    input logic [31:0] value_b,
    output logic [31:0] out_conditional,
    output logic [63:0] out_explicit
);
    assign out_conditional = condition ? value_a : value_b;
    logic [63:0] temp_explicit;
    assign temp_explicit = 64'(value_a) + 64'(value_b);
    assign out_explicit = temp_explicit;
    assign out_explicit = 64'(out_conditional);
endmodule


module ComplexConversions (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [15:0] out_concat
);
    always_comb begin
        out_concat = {in_a, in_b};
    end
endmodule


module module_concat_if (
    input wire [3:0] in_a,
    input wire [3:0] in_b,
    input wire [7:0] in_c,
    input wire in_cond_if,
    output logic [15:0] out_concat,
    output logic [7:0] out_if_else
);
    always_comb begin
    out_concat = {in_a, in_b, in_c};
    if (in_cond_if) begin
        out_if_else = in_c;
    end else begin
        out_if_else = {in_a, in_b};
    end
    end
endmodule


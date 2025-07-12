module Module_BasicSyntax (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic out_cmp,
    output logic [7:0] out_ops
);
    logic [7:0] temp;
    always_comb begin
        temp = in_a + in_b;
    end
    assign out_ops = (in_a & in_b) | (in_a ^ in_b);
    assign out_cmp = (in_a == in_b);
endmodule


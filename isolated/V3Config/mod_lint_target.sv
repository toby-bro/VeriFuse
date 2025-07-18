module mod_lint_target (
    input wire i_a,
    input wire i_b,
    output logic o_sum,
    output logic [7:0] wide_reg
);
    logic l_reg;
    always_comb begin
        l_reg = 1;
        wide_reg = {i_a, i_b};
    end
    assign o_sum = i_a + i_b;
endmodule


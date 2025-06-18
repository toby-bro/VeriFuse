module split_var_candidate (
    input logic [63:0] i_large_data_a,
    input logic [63:0] i_large_data_b,
    output logic [63:0] o_feedback,
    output logic [63:0] o_sum
);
    logic [63:0] r_feedback_reg;
    logic [63:0] r_intermediate;
    always_comb begin
        r_intermediate = i_large_data_a + r_feedback_reg;
        r_feedback_reg = r_intermediate ^ i_large_data_b;
        o_sum = r_intermediate;
        o_feedback = r_feedback_reg;
    end
endmodule


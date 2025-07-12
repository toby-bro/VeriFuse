module generate_lookup_mod #(
    parameter int enable_param = 1
) (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    genvar i;
    logic [7:0] temp_out_glm;
    generate
        if (enable_param == 1) begin : gen_block_if
            static logic [7:0] conditional_var_glm;
            always_comb conditional_var_glm = in_val * 3;
            always_comb temp_out_glm = gen_block_if.conditional_var_glm;
        end else begin : gen_block_else
            always_comb temp_out_glm = in_val + 5;
        end
    endgenerate
    assign out_val = temp_out_glm;
endmodule


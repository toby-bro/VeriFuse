module array_index_diag_mod #(
    parameter int index_param = 0
) (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    genvar i;
    logic [7:0] local_aidm_vars [0:1];
    generate
        for (i = 0; i < 2; i++) begin : gen_blocks
            static logic [7:0] gen_var;
            always_comb gen_var = in_val + i;
            assign local_aidm_vars[i] = gen_var;
        end
    endgenerate
    assign out_val = (index_param >= 0 && index_param < 2) ? local_aidm_vars[index_param] : 8'b0;
endmodule


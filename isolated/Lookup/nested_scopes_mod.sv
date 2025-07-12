module nested_scopes_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    logic [7:0] module_var_nsm = in_val + 1;
    logic [7:0] local_out_val_nsm;
    always_comb begin : block_a
        static logic [7:0] block_a_var_nsm = module_var_nsm + 1;
        begin : block_b
            static logic [7:0] block_b_var_nsm = block_a_var_nsm + 1;
            local_out_val_nsm = block_b_var_nsm;
        end
    end
    assign out_val = local_out_val_nsm;
endmodule


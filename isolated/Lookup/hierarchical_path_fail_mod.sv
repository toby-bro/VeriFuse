module hierarchical_path_fail_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    always_comb begin : block_a
        static logic [7:0] existing_var_hpfm = in_val + 1;
        begin : block_b
            out_val = in_val + block_a.existing_var_hpfm;
        end
    end
endmodule


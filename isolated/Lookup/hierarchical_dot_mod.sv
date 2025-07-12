module hierarchical_dot_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    logic [7:0] middle_var_hdm;
    always_comb begin : outer_block
        static logic [7:0] outer_var_hdm = in_val;
        middle_var_hdm = outer_var_hdm + 1;
        begin : inner_block
            static logic [7:0] inner_var_hdm = outer_block.outer_var_hdm + middle_var_hdm;
            out_val = inner_var_hdm;
        end
    end
endmodule


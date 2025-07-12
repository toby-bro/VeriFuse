module not_a_hierarchical_scope_diag_mod (
    input logic [7:0] in_var,
    output logic [7:0] out_var
);
    logic [7:0] simple_var_nahsdm;
    always_comb simple_var_nahsdm = in_var;
    assign out_var = simple_var_nahsdm;
endmodule


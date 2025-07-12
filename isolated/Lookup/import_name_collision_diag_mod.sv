package my_package_wildcard_a;
    parameter int WILD_PARAM = 30;

    logic [7:0] common_var_a;

endpackage

module import_name_collision_diag_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    import my_package_wildcard_a::*;
    parameter int WILD_PARAM_LOCAL = 50;
    always_comb out_val = in_val + WILD_PARAM_LOCAL;
endmodule


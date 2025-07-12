package my_package_wildcard_a;
    parameter int WILD_PARAM = 30;

    logic [7:0] common_var_a;

endpackage

package my_package_wildcard_b;
    parameter int OTHER_PARAM = 40;

    logic [7:0] common_var_a;

endpackage

module package_import_wildcard_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    import my_package_wildcard_a::*;
    import my_package_wildcard_b::*;
    always_comb begin
        out_val = in_val + WILD_PARAM + OTHER_PARAM;
    end
endmodule


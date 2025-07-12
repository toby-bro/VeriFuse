module package_parameter_access_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    assign out_val = in_val + my_package_explicit::PKG_PARAM;
endmodule


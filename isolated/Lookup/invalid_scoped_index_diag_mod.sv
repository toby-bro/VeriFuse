module invalid_scoped_index_diag_mod (
    input int dummy_in,
    output int out_val
);
    assign out_val = my_package_explicit::PKG_PARAM;
endmodule


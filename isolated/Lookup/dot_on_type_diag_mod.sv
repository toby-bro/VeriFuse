module dot_on_type_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val + type_dot_diag_pkg::pkg_param;
endmodule


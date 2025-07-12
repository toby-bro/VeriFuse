module not_a_generic_class_diag_mod (
    input int dummy_in,
    output int out_val
);
    assign out_val = NonGenericClass::static_prop;
endmodule


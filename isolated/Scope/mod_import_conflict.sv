package pkg_data_types;
    parameter int PKG_PARAM = 50;

    bit enable;
    int count;
    int data;

endpackage

module mod_import_conflict (
    input logic in_b,
    output logic out_b
);
    import pkg_data_types::PKG_PARAM;
    import pkg_data_types::PKG_PARAM;
    assign out_b = in_b;
endmodule


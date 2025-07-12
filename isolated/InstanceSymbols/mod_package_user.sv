module nested_module (
    input logic nm_in,
    output logic nm_out
);
    assign nm_out = nm_in;
endmodule

module mod_package_user (
    input logic pu_in,
    output logic pu_out
);
    nested_module nested_inst (
        .nm_in(pu_in),
        .nm_out(pu_out)
    );
    localparam int LP = my_package::PKG_PARAM;
endmodule


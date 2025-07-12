module MiscExpressions_HierarchicalValue (
    input logic [7:0] in_dummy,
    output logic [7:0] out_hier_param_pkg
);
    assign out_hier_param_pkg = my_package::PKG_PARAM;
endmodule


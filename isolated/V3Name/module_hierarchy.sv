module module_hierarchy (
    output wire h_out_result,
    input wire h_in_a,
    input wire h_in_b
);
    wire hierarchy_internal_wire;
    module_simple instance_of_simple (
        .i_a(h_in_a),
        .i_b(h_in_b),
        .o_c(hierarchy_internal_wire)
    );
    assign h_out_result = hierarchy_internal_wire;
endmodule

module module_simple (
    input wire i_a,
    input wire i_b,
    output wire o_c
);
    wire internal_xor_res;
    assign internal_xor_res = i_a ^ i_b;
    assign o_c = internal_xor_res & i_a;
endmodule


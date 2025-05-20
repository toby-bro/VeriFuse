module module_hierarchy (
    input wire h_in_a,
    input wire h_in_b,
    output wire h_out_result
);
    wire hierarchy_internal_wire;
      module_simple instance_of_simple (
      .i_a(h_in_a),
      .i_b(h_in_b),
      .o_c(hierarchy_internal_wire)
      );
      assign h_out_result = hierarchy_internal_wire;
endmodule


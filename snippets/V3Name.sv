module module_simple (
    input wire i_a,
    input wire i_b,
    output wire o_c
);
  wire internal_xor_res;
  assign internal_xor_res = i_a ^ i_b;
  assign o_c = internal_xor_res & i_a;
endmodule
module module_func (
    input int i_val1,
    input int i_val2,
    output int o_sum_doubled
);
  function automatic int add_and_double_func(input int input_val);
    int func_local_var;
    func_local_var = input_val + 1;
    return func_local_var * 2;
  endfunction
  assign o_sum_doubled = add_and_double_func(i_val1) + i_val2;
endmodule
module module_struct (
    input wire [15:0] i_packed_data,
    output logic [7:0] o_member_sum
);
  typedef struct packed {
    logic [3:0] part1;
    logic [7:0] part2;
    logic [3:0] part3;
  } my_packed_struct_t;
  my_packed_struct_t unpacked_data;
  assign unpacked_data = i_packed_data;
  always @* begin
    o_member_sum = unpacked_data.part1 + unpacked_data.part2 + unpacked_data.part3;
  end
endmodule
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
module module_scope (
    input wire [7:0] s_input_val,
    output logic [7:0] s_output_val
);
  always @* begin : procedural_scope_block
    automatic logic [7:0] local_automatic_reg;
    if (s_input_val > 50) begin
      local_automatic_reg = s_input_val - 10;
    end else begin
      local_automatic_reg = s_input_val + 20;
    end
    s_output_val = local_automatic_reg;
  end : procedural_scope_block
endmodule

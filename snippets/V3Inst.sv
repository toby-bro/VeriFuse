interface my_interface;
  logic [3:0] data_a;
  logic data_b;
endinterface
class MyClass;
  int counter;
  function new();
    counter = 1;
  endfunction
  function int increment(int val);
    counter += val;
    return counter;
  endfunction
endclass
primitive my_udp (d, a, b);
  output d;
  input a, b;
  table
    0 0 : 0;
    0 1 : 1;
    1 0 : 1;
    1 1 : 0;
  endtable
endprimitive
module module_basic(
    input logic in_basic,
    output logic out_basic
);
  assign out_basic = in_basic;
endmodule
module module_const_in(
    input logic [3:0] in_const,
    output logic out_const_any
);
  assign out_const_any = |in_const;
endmodule
module module_output_short_internal(
    input logic in_short_ctrl,
    output logic [7:0] out_short_val
);
  assign out_short_val = 8'h00;
endmodule
module module_arrays(
    input logic [7:0] packed_port_in,
    output logic unpacked_port_out [3:0]
);
  genvar i;
  for (i=0; i<4; i=i+1) begin
    assign unpacked_port_out[i] = packed_port_in[i];
  end
endmodule
module module_interface_user(
    my_interface iface_in,
    output logic out_from_iface
);
  assign out_from_iface = |iface_in.data_a && iface_in.data_b;
endmodule
module module_array_interface_user(
    my_interface iface_array_in [3],
    output logic out_from_iface_array [3]
);
  genvar k;
  for (k=0; k<3; k=k+1) begin
    assign out_from_iface_array[k] = (|iface_array_in[k].data_a) | iface_array_in[k].data_b;
  end
endmodule
module module_assign_interface_array_rhs(
    input my_interface in_if_arr [2],
    output logic out_iface_assign
);
  assign out_iface_assign = in_if_arr[0].data_a[0] ^ in_if_arr[1].data_b;
endmodule
module module_procedural_class(
    input logic clk, reset,
    output int current_counter
);
  MyClass my_class_handle;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      my_class_handle = new();
      current_counter <= my_class_handle.counter;
    end else begin
      if (my_class_handle != null) begin
        current_counter <= my_class_handle.increment(1);
      end else begin
         current_counter <= 0;
      end
    end
  end
endmodule
module module_arrayable(
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
  assign data_out = data_in + 1;
endmodule
module module_const_output_internal(
    input logic in_unused,
    output logic [7:0] out_always_zero
);
  assign out_always_zero = 8'd0;
endmodule
module module_output_only(
    input logic dummy_in,
    output logic [7:0] out_data
);
  assign out_data = 8'b10101010;
endmodule
(* verilator unconnected_drive = 0 *) module module_unconnected_drive_0 (input logic in_a, input logic in_b, output logic out); assign out = in_a; endmodule
(* verilator unconnected_drive = 1 *) module module_unconnected_drive_1 (input logic in_a, input logic in_b, output logic out); assign out = in_a; endmodule
module module_input_extend(input logic [3:0] in_narrow, output logic out_dummy); assign out_dummy = |in_narrow; endmodule
module module_input_select(input logic [7:0] in_wide, output logic out_dummy); assign out_dummy = |in_wide; endmodule
module module_output_to_wider(input logic in_dummy, output logic [3:0] out_narrow); assign out_narrow = {4{in_dummy}}; endmodule
module module_output_to_narrower(input logic in_dummy, output logic [7:0] out_wide); assign out_wide = {8{in_dummy}}; endmodule
module module_input_extend_signed(input signed [3:0] logic in_narrow, output logic out_dummy); assign out_dummy = |in_narrow; endmodule
module module_input_select_signed(input signed [7:0] logic in_wide, output logic out_dummy); assign out_dummy = |in_wide; endmodule
module module_output_to_wider_signed(input logic in_dummy, output signed [3:0] logic out_narrow); assign out_narrow = $signed({4{in_dummy}}); endmodule
module module_output_to_narrower_signed(input logic in_dummy, output signed [7:0] logic out_wide); assign out_wide = $signed({8{in_dummy}}); endmodule
module module_interface_holder(
    input logic dummy_in,
    output logic dummy_out
);
  my_interface internal_if_array [1:0];
  assign dummy_out = dummy_in;
  assign internal_if_array[0].data_a = {4{dummy_in}};
  assign internal_if_array[0].data_b = dummy_in;
  assign internal_if_array[1].data_a = internal_if_array[0].data_a;
  assign internal_if_array[1].data_b = internal_if_array[0].data_b;
endmodule
module module_interface_copier(
    input my_interface in_arr_b [1:0],
    output my_interface out_arr_a [1:0]
);
  assign out_arr_a = in_arr_b;
endmodule
module module_width_mismatch(
    input logic [15:0] in_wide,
    input logic [3:0] in_narrow,
    output logic [7:0] out_mixed
);
  logic [7:0] temp_wire;
  assign temp_wire = {in_wide[7:0], in_narrow};
  assign out_mixed = temp_wire;
endmodule
module instantiation_test(
    input logic clk, reset,
    input logic basic_in,
    input logic short_ctrl_in,
    input logic [15:0] mismatch_wide_in,
    input logic [7:0] arrays_packed_in,
    output logic basic_out,
    output logic const_any_out,
    output logic [7:0] short_val_out,
    output logic arrays_unpacked_out [3:0],
    output logic iface_user_out,
    output logic iface_array_user_out [3],
    output logic iface_assign_out,
    output int class_counter_out,
    output logic [7:0] arrayable_out_combined,
    output logic [7:0] const_output_val_internal,
    output logic [7:0] output_only_val,
    output logic udp_out_top,
    output my_interface iface_copier_out_arr [1:0],
    output logic [1:0] iface_array_slice_rhs_wire,
    output logic [7:0] mismatch_mixed_out
);
  logic [3:0] const_in_sig;
  logic [3:0] mismatch_narrow_sig;
  logic arrays_unpacked_wire [3:0];
  logic const_in_lit_out;
  logic udp_out;
  logic undriven_out_0;
  logic undriven_out_1;
  logic [15:0] arrayable_packed_in;
  logic [7:0] arrayable_inst_outs [0:1];
  logic [7:0] arrayable_inst_outs_packed [0:1];
  logic [7:0] slice_source = 8'hAA;
  logic [3:0] slice_dest;
  logic [3:0] part_select_source [1:0];
  logic part_select_dest;
  my_interface iface_sig();
  my_interface iface_array_sig[4]();
  my_interface iface_array_sig2[1:0];
  logic [3:0] sig_4;
  logic [7:0] sig_8;
  logic [15:0] sig_16;
  signed [3:0] logic sig_s4;
  signed [7:0] logic sig_s8;
  signed [15:0] logic sig_s16;
  logic dummy_out_wires [8];
  logic output_only_wire;
  assign const_in_sig = 4'd10;
  assign mismatch_narrow_sig = 4'd3;
  assign arrayable_packed_in = { {8{short_ctrl_in}}, {8{basic_in}} };
  assign slice_dest = slice_source[7:4];
  assign part_select_source[0] = 4'b1010;
  assign part_select_source[1] = 4'b0101;
  assign part_select_dest = part_select_source[0][2];
  assign output_only_wire = 8'hFF;
  assign sig_4 = 4'hA;
  assign sig_8 = 8'h5A;
  assign sig_16 = 16'h1234;
  assign sig_s4 = -'sh4;
  assign sig_s8 = -'sh5A;
  assign sig_s16 = -'sh1234;
  assign iface_sig.data_a = {4{basic_in}};
  assign iface_sig.data_b = basic_in;
  genvar j;
  for (j=0; j<4; j=j+1) begin : iface_array_conn
    assign iface_array_sig[j].data_a = {4{basic_in}};
    assign iface_array_sig[j].data_b = short_ctrl_in;
  end
  assign iface_array_sig2[0].data_a = 4'h1; assign iface_array_sig2[0].data_b = 1'b1;
  assign iface_array_sig2[1].data_a = 4'h2; assign iface_array_sig2[1].data_b = 1'b0;
  assign iface_array_slice_rhs_wire = iface_array_sig[0].data_a[1+:2];
  module_basic basic_inst(
      .in_basic(basic_in),
      .out_basic(basic_out)
  );
  module_const_in const_inst(
      .in_const(const_in_sig),
      .out_const_any(const_any_out)
  );
  module_const_in const_inst_lit(
      .in_const(4'hF),
      .out_const_any(const_in_lit_out)
  );
  assign const_any_out = const_any_out | const_in_lit_out;
  module_output_short_internal short_inst(
      .in_short_ctrl(short_ctrl_in),
      .out_short_val(short_val_out)
  );
  module_width_mismatch mismatch_inst(
      .in_wide(mismatch_wide_in),
      .in_narrow(mismatch_narrow_sig),
      .out_mixed(mismatch_mixed_out)
  );
  module_arrays arrays_inst(
      .packed_port_in(arrays_packed_in),
      .unpacked_port_out(arrays_unpacked_wire)
  );
  genvar l;
  for (l=0; l<4; l=l+1) begin : assign_unpacked_loop
    assign arrays_unpacked_out[l] = arrays_unpacked_wire[l];
  end
  module_interface_user iface_user_inst(
      .iface_in(iface_sig),
      .out_from_iface(iface_user_out)
  );
  module_interface_user iface_user_inst_single_array_element(
      .iface_in(iface_array_sig[0]),
      .out_from_iface(dummy_out_wires[0])
  );
  module_array_interface_user iface_array_user_inst(
      .iface_array_in(iface_array_sig[0+:3]),
      .out_from_iface_array(iface_array_user_out)
  );
  module_assign_interface_array_rhs iface_assign_inst(
      .in_if_arr(iface_array_sig[2+:2]),
      .out_iface_assign(iface_assign_out)
  );
  module_procedural_class class_inst(
      .clk(clk),
      .reset(reset),
      .current_counter(class_counter_out)
  );
  module_arrayable arrayable_inst[0:1](
      .data_in({8{basic_in}}),
      .data_out(arrayable_inst_outs)
  );
   module_arrayable arrayable_inst_packed[0:1](
      .data_in(arrayable_packed_in),
      .data_out(arrayable_inst_outs_packed)
   );
  assign arrayable_out_combined = arrayable_inst_outs[0] | arrayable_inst_outs_packed[0] | arrayable_inst_outs_packed[1];
  module_const_output_internal const_output_inst(
      .in_unused(basic_in),
      .out_always_zero(const_output_val_internal)
  );
  module_output_only output_only_inst(
      .dummy_in(basic_in),
      .out_data(output_only_val)
  );
  my_udp udp_inst(
    .d(udp_out),
    .a(basic_in),
    .b(short_ctrl_in)
  );
  assign udp_out_top = udp_out;
  module_unconnected_drive_0 undriven_inst_0(.in_a(basic_in), .out(undriven_out_0));
  module_unconnected_drive_1 undriven_inst_1(.in_a(basic_in), .out(undriven_out_1));
  assign basic_out = basic_out | undriven_out_0 | undriven_out_1;
  module_input_select input_extend_u_inst(.in_wide(sig_4), .out_dummy(dummy_out_wires[1]));
  module_input_extend input_select_u_inst(.in_narrow(sig_8), .out_dummy(dummy_out_wires[2]));
  assign sig_8 = output_extend_u_inst.out_narrow;
  module_output_to_wider output_extend_u_inst(.in_dummy(basic_in), .out_narrow());
  assign sig_4 = output_select_u_inst.out_wide;
  module_output_to_narrower output_select_u_inst(.in_dummy(basic_in), .out_wide());
  module_input_select_signed input_extend_s_inst(.in_wide(sig_s4), .out_dummy(dummy_out_wires[3]));
  module_input_extend_signed input_select_s_inst(.in_narrow(sig_s8), .out_dummy(dummy_out_wires[4]));
  assign sig_s8 = output_extend_s_inst.out_narrow;
  module_output_to_wider_signed output_extend_s_inst(.in_dummy(basic_in), .out_narrow());
  assign sig_s4 = output_select_s_inst.out_wide;
  module_output_to_narrower_signed output_select_s_inst(.in_dummy(basic_in), .out_wide());
  module_interface_holder interface_holder_inst(.dummy_in(basic_in), .dummy_out(dummy_out_wires[5]));
  module_interface_copier interface_copier_inst(.in_arr_b(iface_array_sig2), .out_arr_a(iface_copier_out_arr));
endmodule

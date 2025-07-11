interface my_if;
  logic signal_a;
  logic signal_b;
  modport mp (
    input signal_a,
    output signal_b
  );
endinterface
interface my_if_array;
  logic [7:0] data;
endinterface
typedef enum {RED, GREEN} my_enum_t;
typedef struct { int x; } struct_x_t;
module ansi_basic (
  input logic clk,
  output logic reset_n
);
  always_comb begin
    reset_n = clk;
  end
endmodule
module ansi_types (
  input int data_int,
  output real data_real,
  input logic [7:0] byte_in,
  output bit [7:0] byte_out
);
  always_comb begin
    byte_out = byte_in + 1;
    data_real = data_int;
  end
endmodule
module ansi_directions (
  inout wire data_inout,
  input logic data_ref_in,
  output logic data_ref_out,
  input logic control_in,
  output logic status_out
);
  logic internal_data = 1'b0;
  assign data_inout = internal_data;
  always_comb begin
    data_ref_out = data_ref_in;
    internal_data = data_inout;
    status_out = internal_data | control_in;
  end
endmodule
module ansi_arrays (
  input logic [3:0] input_array,
  output logic [7:0][1:0] output_array
);
  always_comb begin
    output_array[0] = {input_array, input_array};
    output_array[1] = {input_array[3:2], input_array[1:0]};
  end
endmodule
module ansi_implicit_inherit (
  input logic [2:0] in1,
  input in2,
  output logic out1,
  output logic out2,
  output logic extra_out
);
  always_comb begin
    out1 = |in1;
    out2 = |in2;
    extra_out = out1 ^ out2;
  end
endmodule
module non_ansi_basic (
  non_ansi_a,
  non_ansi_b,
  non_ansi_basic_input,
  non_ansi_basic_output
);
  input wire non_ansi_a;
  output reg non_ansi_b;
  input logic non_ansi_basic_input;
  output logic non_ansi_basic_output;
  always_comb begin
    non_ansi_b = non_ansi_a;
    non_ansi_basic_output = non_ansi_basic_input;
  end
endmodule
module non_ansi_types (
  non_ansi_c,
  non_ansi_d,
  non_ansi_types_input,
  non_ansi_types_output
);
  input struct_x_t non_ansi_c;
  output my_enum_t non_ansi_d;
  input logic non_ansi_types_input;
  output logic non_ansi_types_output;
  my_enum_t d_local;
  struct_x_t c_local;
  assign non_ansi_types_output = non_ansi_types_input;
  always_comb begin
    c_local = non_ansi_c;
    d_local = non_ansi_d;
    non_ansi_d = d_local;
  end
endmodule
module non_ansi_nets (
  non_ansi_e,
  non_ansi_f,
  non_ansi_nets_input,
  non_ansi_nets_output
);
  input trireg non_ansi_e;
  inout wire non_ansi_f; // changed from uwire to wire
  input logic non_ansi_nets_input;
  output logic non_ansi_nets_output;
  assign non_ansi_f = non_ansi_e;
  assign non_ansi_nets_output = non_ansi_nets_input;
endmodule
module non_ansi_init (
  non_ansi_g,
  non_ansi_h,
  non_ansi_init_input,
  non_ansi_init_output
);
  output logic non_ansi_g = 1'b1;
  output logic non_ansi_h = 1'b0;
  input logic non_ansi_init_input;
  output logic non_ansi_init_output;
  assign non_ansi_init_output = non_ansi_init_input;
endmodule
module non_ansi_concat_port (
  {non_ansi_i, non_ansi_j},
  concat_port_input,
  concat_port_output
);
  output logic [1:0] non_ansi_i;
  output logic [1:0] non_ansi_j;
  input logic concat_port_input;
  output logic concat_port_output;
  assign non_ansi_i = 2'b10;
  assign non_ansi_j = 2'b01;
  assign concat_port_output = concat_port_input;
endmodule
module ansi_interface_port (
  my_if iface_port,
  input logic interface_input,
  output logic interface_output
);
  always_comb begin
    iface_port.signal_b = iface_port.signal_a;
    interface_output = interface_input;
  end
endmodule
module ansi_interface_port_modport (
  my_if.mp iface_port_mp,
  input logic modport_input,
  output logic modport_output
);
  always_comb begin
    iface_port_mp.signal_b = iface_port_mp.signal_a;
    modport_output = modport_input;
  end
endmodule
module non_ansi_interface_port (
  k,
  non_ansi_if_input,
  non_ansi_if_output
);
  my_if k;
  input logic non_ansi_if_input;
  output logic non_ansi_if_output;
  assign non_ansi_if_output = non_ansi_if_input;
  always_comb begin
    k.signal_b = k.signal_a;
  end
endmodule
module child_simple (
  input logic in1,
  inout wire io1,
  output logic out1
);
  assign io1 = in1 & out1;
  always_comb begin
    out1 = in1 ^ io1;
  end
endmodule
module child_concat_output (
  input logic dummy_in,
  output logic [7:0] data
);
  assign data = dummy_in ? 8'hAA : 8'h55;
endmodule
module child_iface_port (
  my_if if_inst,
  input logic iface_child_input,
  output logic iface_child_output
);
  assign if_inst.signal_b = ~if_inst.signal_a;
  assign iface_child_output = iface_child_input;
endmodule
module child_defaults (
  input int val_in = 10,
  output bit flag_out,
  input logic dummy_in
);
  always_comb begin
    flag_out = (val_in > 5) ^ dummy_in;
  end
endmodule
module udnt_port_module (
  input logic uin,
  output logic uout,
  input logic udnt_input,
  output logic udnt_output
);
  assign uout = uin;
  assign udnt_output = udnt_input;
endmodule
module simple_child_for_implicit (
  input logic in1,
  inout wire io1,
  output logic out1
);
  assign io1 = in1 & out1;
  always_comb begin
    out1 = in1 ^ io1;
  end
endmodule
module explicit_ansi_ports_module (
  input .explicit_in_p(in_explicit),
  output .explicit_out_p(out_explicit),
  input logic dummy_in_ansi,
  output logic dummy_out_ansi
);
  logic in_explicit;
  logic out_explicit;
  always_comb begin
    out_explicit = in_explicit;
    dummy_out_ansi = dummy_in_ansi;
  end
endmodule
module explicit_non_ansi_ports_module (
  named_conn_in,
  named_conn_out,
  dummy_in_non_ansi,
  dummy_out_non_ansi
);
  input logic named_conn_in;
  output logic named_conn_out;
  input logic dummy_in_non_ansi;
  output logic dummy_out_non_ansi;
  assign named_conn_out = named_conn_in;
  assign dummy_out_non_ansi = dummy_in_non_ansi;
endmodule
module explicit_non_ansi_decl_module (p_in, p_out);
  input logic p_in;
  output wire p_out;
  assign p_out = p_in;
endmodule
module child_empty_ports (p1, , p2);
  input logic p1;
  output logic p2;
  assign p2 = p1;
endmodule
module net_var_conn_child (
  input logic in_logic,
  output logic out_wire
);
  assign out_wire = in_logic;
endmodule
module multi_port_decl_module (
  input logic [3:0] p_a,
  input logic [3:0] p_b,
  input logic single_in,
  output logic single_out
);
  always_comb begin
    // Assign to outputs only
    single_out = single_in;
  end
endmodule
module mixed_conn_child (
  input logic [7:0] data_in,
  input logic dummy_in,
  output logic dummy_out
);
  logic dummy_internal;
  always_comb dummy_internal = |data_in | dummy_in;
  assign dummy_out = dummy_internal;
endmodule
module iface_array_port_child (
  my_if_array iface_array_port [1:0],
  input logic array_in,
  output logic array_out
);
  always_comb begin
    iface_array_port[0].data = array_in ? 8'hAA : 8'h55;
    iface_array_port[1].data = array_in ? 8'h55 : 8'hAA;
    array_out = array_in;
  end
endmodule
module port_connection_tester (
  input logic global_clk,
  output wire final_status,
  input logic tester_dummy_in,
  output logic tester_dummy_out
);
  logic explicit_ansi_in_conn;
  wire explicit_ansi_out_conn;
  logic simple_in_ord = 1'b0;
  wire simple_io_ord;
  logic simple_out_ord;
  logic in1;
  wire io1;
  logic out1;
  assign in1 = global_clk;
  logic empty_named_out;
  wire [7:0] concat_dest_wire;
  my_if iface_inst();
  my_if iface_child_if();
  bit default_flag_unconnected;
  bit default_flag_connected;
  int default_val_conn = 25;
  wire udnt_wire_conn;
  logic udnt_logic_assigned;
  logic udnt_local_net;
  assign udnt_wire_conn = global_clk;
  logic empty_p1_in = 1'b1;
  logic empty_p2_out;
  logic logic_sig = 1'b0;
  wire wire_sig;
  wire net_a = 1'b1;
  logic var_b = 1'b0;
  wire [3:0] net_c = 4'b1111;
  logic [2:0] var_d = 3'b001;
  logic concat_named_a_part; 
  logic concat_named_b_part;
  logic concat_named_in = 1'b1;
  logic concat_named_out;
  logic local_named_conn_in = 1'b1;
  assign simple_io_ord = simple_in_ord | simple_out_ord;
  assign io1 = global_clk & out1;
  assign udnt_logic_assigned = udnt_local_net;
  assign wire_sig = logic_sig;
  assign tester_dummy_out = tester_dummy_in;
  child_simple ordered_inst (
    simple_in_ord,
    simple_io_ord,
    simple_out_ord
  );
  simple_child_for_implicit implicit_inst (
    .in1(in1),
    .io1(io1),
    .out1(out1)
  );
  child_simple empty_named_inst (
    .in1(1'b1),
    .io1(),
    .out1(empty_named_out)
   );
  child_concat_output concat_inst (
    .data({concat_dest_wire[3:0], concat_dest_wire[7:4]}),
    .dummy_in(global_clk)
  );
  logic iface_child_output_wire;
  child_iface_port iface_child_inst (
    .if_inst(iface_child_if),
    .iface_child_input(global_clk),
    .iface_child_output(iface_child_output_wire)
  );
  always_comb begin
      iface_child_if.signal_a = global_clk;
  end
  child_defaults default_inst_unconnected (
    .flag_out(default_flag_unconnected),
    .dummy_in(global_clk)
  );
  child_defaults default_inst_connected (
    .val_in(default_val_conn),
    .flag_out(default_flag_connected),
    .dummy_in(global_clk)
  );
  udnt_port_module udnt_inst (
    .uin(udnt_wire_conn),
    .uout(udnt_local_net),
    .udnt_input(global_clk),
    .udnt_output()
  );
  explicit_ansi_ports_module explicit_ansi_inst (
      .explicit_in_p(explicit_ansi_in_conn),
      .explicit_out_p(explicit_ansi_out_conn),
      .dummy_in_ansi(global_clk),
      .dummy_out_ansi()
  );
  explicit_non_ansi_ports_module explicit_non_ansi_inst (
      .named_conn_in(local_named_conn_in),
      .named_conn_out(final_status),
      .dummy_in_non_ansi(global_clk),
      .dummy_out_non_ansi()
  );
  child_empty_ports empty_port_inst (empty_p1_in, , empty_p2_out);
  net_var_conn_child net_var_inst (.in_logic(logic_sig), .out_wire(wire_sig));
  mixed_conn_child mixed_inst (
    .data_in({net_a, var_b, net_c, var_d}),
    .dummy_in(global_clk),
    .dummy_out() 
  );
  multi_port_decl_module named_concat_port_inst (
      .p_a(concat_named_a_part), 
      .p_b(concat_named_b_part),
      .single_in(concat_named_in),
      .single_out(concat_named_out)
  );
  assign concat_named_a_part = 4'hC;
  assign concat_named_b_part = 4'hD;
endmodule
module wrapper_module;
  logic clk = 1'b1;
  logic basic_reset_n;
  int types_int_in = 42;
  real types_real_out;
  logic [7:0] types_byte_in = 8'hFF;
  bit [7:0] types_byte_out;
  wire directions_inout;
  logic directions_ref_in_logic;
  logic directions_ref_out;
  logic directions_control_in = 1'b1;
  logic directions_status_out;
  logic [3:0] arrays_input = 4'b1100;
  logic [7:0][1:0] arrays_output;
  logic [2:0] implicit_in1 = 3'b010;
  logic implicit_in2 = 1'b0;
  logic implicit_out1, implicit_out2, implicit_extra_out;
  wire non_ansi_basic_a = 1'b1;
  reg non_ansi_basic_b;
  logic non_ansi_basic_in = 1'b0;
  logic non_ansi_basic_out;
  struct_x_t non_ansi_types_c = '{x: 100};
  my_enum_t non_ansi_types_d;
  logic non_ansi_types_in = 1'b1;
  logic non_ansi_types_out;
  trireg non_ansi_nets_e = 1'b0;
  wire non_ansi_nets_f;
  logic non_ansi_nets_in = 1'b0;
  logic non_ansi_nets_out;
  logic non_ansi_init_g, non_ansi_init_h;
  logic non_ansi_init_in = 1'b1;
  logic non_ansi_init_out;
  logic [1:0] concat_i, concat_j;
  logic concat_port_in = 1'b0;
  logic concat_port_out;
  my_if ansi_iface_inst();
  logic ansi_iface_input = 1'b1;
  logic ansi_iface_output;
  my_if ansi_modport_iface_inst();
  logic ansi_modport_input = 1'b0;
  logic ansi_modport_output;
  my_if non_ansi_iface_inst();
  logic non_ansi_iface_input = 1'b1;
  logic non_ansi_iface_output;
  logic tester_clk = 1'b1;
  wire tester_status;
  logic tester_dummy_in = 1'b0;
  logic tester_dummy_out;
  logic tester_explicit_ansi_in;
  wire tester_explicit_ansi_out;
  logic explicit_non_ansi_decl_in;
  wire explicit_non_ansi_decl_out;
  my_if_array iface_array_inst [1:0]();
  logic iface_array_in = 1'b0;
  logic iface_array_out;
  logic local_logic_var = 1'b0;
  logic iconn_child_in = 1'b1;
  logic iconn_child_out;
  logic iconn_child_in_v = 1'b1;
  logic iconn_child_out_v;
  ansi_basic inst_basic (
    .clk(clk),
    .reset_n(basic_reset_n)
  );
  ansi_types inst_types (
    .data_int(types_int_in),
    .data_real(types_real_out),
    .byte_in(types_byte_in),
    .byte_out(types_byte_out)
  );
  ansi_directions inst_directions (
    .data_inout(directions_inout),
    .data_ref_in(directions_ref_in_logic),
    .data_ref_out(directions_ref_out),
    .control_in(directions_control_in),
    .status_out(directions_status_out)
  );
  assign directions_inout = 1'b0;
  assign directions_ref_in_logic = 1'b0;
  ansi_arrays inst_arrays (
    .input_array(arrays_input),
    .output_array(arrays_output)
  );
  ansi_implicit_inherit inst_implicit (
    .in1(implicit_in1),
    .in2(implicit_in2),
    .out1(implicit_out1),
    .out2(implicit_out2),
    .extra_out(implicit_extra_out)
  );
  non_ansi_basic inst_non_ansi_basic (
    non_ansi_basic_a,
    non_ansi_basic_b,
    non_ansi_basic_in,
    non_ansi_basic_out
  );
  non_ansi_types inst_non_ansi_types (
    non_ansi_types_c,
    non_ansi_types_d,
    non_ansi_types_in,
    non_ansi_types_out
  );
  non_ansi_nets inst_non_ansi_nets (
    non_ansi_nets_e,
    non_ansi_nets_f,
    non_ansi_nets_in,
    non_ansi_nets_out
  );
  non_ansi_init inst_non_ansi_init (
    non_ansi_init_g,
    non_ansi_init_h,
    non_ansi_init_in,
    non_ansi_init_out
  );
  non_ansi_concat_port inst_non_ansi_concat (
    {concat_i, concat_j},
    concat_port_in,
    concat_port_out
  );
  ansi_interface_port inst_ansi_if (
    .iface_port(ansi_iface_inst),
    .interface_input(ansi_iface_input),
    .interface_output(ansi_iface_output)
  );
  assign ansi_iface_inst.signal_a = clk;
  ansi_interface_port_modport inst_ansi_if_mp (
    .iface_port_mp(ansi_modport_iface_inst.mp),
    .modport_input(ansi_modport_input),
    .modport_output(ansi_modport_output)
  );
  assign ansi_modport_iface_inst.signal_a = clk;
  non_ansi_interface_port inst_non_ansi_if (
    non_ansi_iface_inst,
    non_ansi_iface_input,
    non_ansi_iface_output
  );
  assign non_ansi_iface_inst.signal_a = clk;
  port_connection_tester inst_tester (
    .global_clk(tester_clk),
    .final_status(tester_status),
    .tester_dummy_in(tester_dummy_in),
    .tester_dummy_out(tester_dummy_out)
  );
  explicit_non_ansi_decl_module inst_explicit_non_ansi_decl (
    explicit_non_ansi_decl_in,
    explicit_non_ansi_decl_out
  );
  iface_array_port_child inst_iface_array (
    .iface_array_port(iface_array_inst),
    .array_in(iface_array_in),
    .array_out(iface_array_out)
  );
  udnt_port_module udnt_inst (
    .uin(udnt_wire_conn),
    .uout(udnt_local_net),
    .udnt_input(global_clk),
    .udnt_output()
  );
  explicit_ansi_ports_module explicit_ansi_inst (
      .explicit_in_p(explicit_ansi_in_conn),
      .explicit_out_p(explicit_ansi_out_conn),
      .dummy_in_ansi(global_clk),
      .dummy_out_ansi()
  );
  explicit_non_ansi_ports_module explicit_non_ansi_inst (
      .named_conn_in(local_named_conn_in),
      .named_conn_out(final_status),
      .dummy_in_non_ansi(global_clk),
      .dummy_out_non_ansi()
  );
  child_empty_ports empty_port_inst (empty_p1_in, , empty_p2_out);
  net_var_conn_child net_var_inst (.in_logic(logic_sig), .out_wire(wire_sig));
  mixed_conn_child mixed_inst (
    .data_in({net_a, var_b, net_c, var_d}),
    .dummy_in(global_clk),
    .dummy_out() 
  );
  multi_port_decl_module named_concat_port_inst (
      .p_a(concat_named_a_part), 
      .p_b(concat_named_b_part),
      .single_in(concat_named_in),
      .single_out(concat_named_out)
  );
  assign concat_named_a_part = 4'hC;
  assign concat_named_b_part = 4'hD;
endmodule

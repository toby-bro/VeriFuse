typedef struct packed {
  logic [15:0] id;
  int count;
} my_packed_struct_type;
package my_package;
  (* public *) parameter int PACKAGE_PUBLIC_PARAM = 100;
  (* public *) int package_public_int = 42;
  class MyPackageClass;
    int class_val_in_pkg = 0;
    function void setVal(int v);
      class_val_in_pkg = v;
    endfunction
  endclass
  export "DPI-C" function pkg_exported_func;
  function automatic pkg_exported_func(input int val);
    return val * 5;
  endfunction
endpackage : my_package;
module module_basic (
  input bit in_basic,
  output bit out_basic
);
  logic internal_sig;
  always_comb begin
    internal_sig = in_basic;
  end
  assign out_basic = internal_sig;
endmodule : module_basic
module module_params_public_vars (
  input bit clk_in,
  input int in_int,
  output real out_real
);
  parameter int P_INT = 10;
  const parameter real LP_REAL = 3.14;
  (* public *) logic [7:0] public_byte;
  (* public *) real public_real;
  public string public_string = "default string";
  public enum {RED, GREEN, BLUE} public_enum;
  public struct packed {
    logic flag;
    int value;
    logic [3:0] nibble;
  } public_packed_struct;
  public int public_unpacked_array_int [2][3];
  public logic [31:0] public_unpacked_packed_array_logic [5];
  public shortint public_shortint_var;
  public longint public_longint_var;
  public byte public_byte_var;
  public bit [63:0] public_bit_64;
  public logic public_logic_1;
  public logic [15:0] public_logic_16;
  public signed int public_signed_int;
  typedef struct { bit valid; logic [7:0] data; } my_unpacked_struct_type;
  public my_unpacked_struct_type public_unpacked_struct_array [4];
  wire [7:0] bitwise_result;
  wire [31:0] shifted_value;
  wire [7:0] unary_result;
  wire [15:0] concat_result;
  wire [7:0] slice_result;
  wire enum_comparison_val;
  assign public_real = $itor(in_int) * LP_REAL;
  assign public_signed_int = $signed(in_int);
  assign bitwise_result = ($cast(logic[7:0], in_int) | 8'hAA) ^ 8'h55;
  assign shifted_value = $cast(logic[31:0], in_int) <<< 2;
  assign unary_result = ~public_byte;
  assign concat_result = {public_byte, bitwise_result};
  assign slice_result = public_unpacked_packed_array_logic[0][7:0];
  assign enum_comparison_val = (public_enum == GREEN) && (public_enum != RED);
  assign out_real = public_real + $sin($itor(in_int)) + $itor(bitwise_result) + $itor(unary_result) + $itor(public_shortint_var) + $itor($cast(int, public_longint_var)) + $itor($cast(int, public_byte_var)) + $itor($cast(int, public_bit_64)) + $itor($cast(int, public_logic_1)) + $itor($cast(int, public_logic_16)) + $itor(public_signed_int);
  always @(posedge clk_in) begin
      public_byte = in_int % 256;
      public_enum = (in_int % 3 == 0) ? RED : (in_int % 3 == 1) ? GREEN : BLUE;
      public_string = (in_int > 100) ? "large" : "small";
      public_shortint_var = $cast(shortint, in_int);
      public_longint_var = $cast(longint, in_int) * 100;
      public_byte_var = $cast(byte, in_int % 256);
      public_bit_64 = $cast(bit[63:0], in_int) + 100;
      public_logic_1 = $cast(logic, in_int % 2);
      public_logic_16 = $cast(logic[15:0], in_int + 256);
      public_packed_struct.flag = (in_int > P_INT) || (in_int < 0);
      public_packed_struct.value = in_int + P_INT - 1;
      public_packed_struct.nibble = $cast(logic[3:0], in_int & 4'hF);
      if (in_int inside {[0:5]}) begin
          public_unpacked_array_int[in_int % 2][in_int % 3] = in_int * 2;
          public_unpacked_packed_array_logic[in_int % 5] = $cast(logic[31:0], in_int) + 1;
          public_unpacked_struct_array[in_int % 4].valid = 1'b1;
          public_unpacked_struct_array[in_int % 4].data = $cast(logic[7:0], in_int);
      end else begin
          public_unpacked_array_int[0][0] = in_int * 3;
          public_unpacked_packed_array_logic[0] = $cast(logic[31:0], in_int) + 2;
          public_unpacked_struct_array[0].valid = 1'b0;
          public_unpacked_struct_array[0].data = 8'h00;
      end
  end
endmodule : module_params_public_vars
module module_dpi (
  input bit clk_in,
  input int in_dpi_int,
  input real in_dpi_real,
  input logic [7:0] in_dpi_byte,
  output int out_dpi_int,
  output real out_dpi_real,
  output logic [7:0] out_dpi_byte,
  output int out_task_int,
  output real out_task_real,
  output logic [7:0] out_task_byte
);
  import "DPI-C" function int c_add_one(input int arg);
  import "DPI-C" function real c_multiply_real(input real arg1, input real arg2);
  import "DPI-C" function logic [7:0] c_byte_swap(input logic [7:0] arg);
  import "DPI-C" task c_process_value(input int val_in, output int val_out);
  import "DPI-C" task c_process_real(input real val_in, output real val_out);
  import "DPI-C" task c_process_byte(input logic [7:0] val_in, output logic [7:0] val_out);
  export "DPI-C" function sv_add_ports;
  export "DPI-C" function sv_divide_real;
  export "DPI-C" function sv_byte_reverse;
  export "DPI-C" task sv_task_example_int;
  export "DPI-C" task sv_task_example_real;
  export "DPI-C" task sv_task_example_byte;
  function automatic sv_add_ports(input int a, input int b);
    return a + b;
  endfunction
  function automatic sv_divide_real(input real a, input real b);
    return a / b;
  endfunction
  function automatic sv_byte_reverse(input logic [7:0] a);
    logic [7:0] reversed;
    for (int i = 0; i < 8; i++) begin
      reversed[i] = a[7 - i];
    end
    return reversed;
  endfunction
  task automatic sv_task_example_int(input int value_in, output int value_out);
    value_out = value_in + 10;
  endtask
  task automatic sv_task_example_real(input real value_in, output real value_out);
    value_out = value_in * 2.0;
  endtask
  task automatic sv_task_example_byte(input logic [7:0] value_in, output logic [7:0] value_out);
    value_out = value_in | 8'hF0;
  endtask
  wire real out_dpi_real_w;
  wire logic [7:0] out_dpi_byte_w;
  assign out_dpi_int = c_add_one(in_dpi_int);
  assign out_dpi_real_w = c_multiply_real(in_dpi_real, 2.0);
  assign out_dpi_byte_w = c_byte_swap(in_dpi_byte);
  assign out_dpi_real = out_dpi_real_w;
  assign out_dpi_byte = out_dpi_byte_w;
  always @(posedge clk_in) begin
    int task_int_result;
    real task_real_result;
    logic [7:0] task_byte_result;
    c_process_value(in_dpi_int, task_int_result);
    c_process_real(in_dpi_real, task_real_result);
    c_process_byte(in_dpi_byte, task_byte_result);
    out_task_int = task_int_result;
    out_task_real = task_real_result;
    out_task_byte = task_byte_result;
  end
endmodule : module_dpi
module module_coverage (
  input bit clk_in,
  input bit reset_in,
  input logic [1:0] in_cov_state,
  input logic [3:0] in_cov_data,
  output bit out_cov_dummy
);
  state_data_cg cg_instance;
  assign out_cov_dummy = 1'b0;
  covergroup state_data_cg @(posedge clk_in);
    state_cp : coverpoint in_cov_state {
      bins state_0 = {0};
      bins state_1 = {1};
      bins states_2_3 = {2, 3};
    }
    data_cp : coverpoint in_cov_data {
      bins data_low = {[0:7]};
      bins data_high = {[8:15]};
    }
    state_data_cross : cross state_cp, data_cp;
  endgroup
  always @(posedge clk_in or posedge reset_in) begin
    if (reset_in) begin
      cg_instance = new();
    end else begin
      if (cg_instance != null) begin
        cg_instance.sample();
      end
    end
  end
endmodule : module_coverage
module module_time (
  input bit in_time,
  output bit out_time
);
  timeunit 1ns;
  timeprecision 1ps;
  assign out_time = in_time;
endmodule : module_time
module module_events (
  input bit in_event_trigger,
  input bit in_event_assign_val,
  output bit out_event_fired
);
  event my_event;
  logic event_fired_reg = 0;
  always @(posedge in_event_trigger) begin
    -> my_event;
  end
  always_comb begin
      my_event = in_event_assign_val;
  end
  always @(my_event) begin
      event_fired_reg = ~event_fired_reg;
  end
  assign out_event_fired = event_fired_reg;
endmodule : module_events
module module_class (
  input bit in_class_en,
  input int in_class_val,
  output int out_class_val
);
  class MySimpleClass;
    int value = 0;
    real real_value = 0.0;
    function void setValue(int v, real rv);
      this.value = v * 2;
      this.real_value = rv / 2.0;
    endfunction
    function int getValue();
      return value + 1;
    endfunction
  endclass
  MySimpleClass class_h;
  always @(posedge in_class_en) begin
    if (class_h == null) begin
      class_h = new();
    end
    if (class_h != null) begin
        class_h.setValue(in_class_val, $itor(in_class_val) + 0.5);
    end
  end
  assign out_class_val = (class_h != null) ? class_h.getValue() : 0;
endmodule : module_class
module module_with_named_block (
  input bit en,
  output int out
);
  int internal_val = 10;
  always @(en) begin : my_named_block
    int block_val = 5;
    if (en) begin
      internal_val = internal_val + block_val;
    end else begin
      internal_val = internal_val - block_val;
    end
  end : my_named_block
  assign out = internal_val;
endmodule : module_with_named_block
module module_with_typedef (
  input bit clk,
  input int in_count,
  output bit [15:0] out_id
);
  public my_packed_struct_type public_typed_var;
  always @(posedge clk) begin
    public_typed_var.id = $cast(logic[15:0], in_count);
    public_typed_var.count = in_count;
  end
  assign out_id = public_typed_var.id;
endmodule : module_with_typedef
module module_in_package (
  input bit in_pkg_mod,
  output bit out_pkg_mod
);
  assign out_pkg_mod = in_pkg_mod;
endmodule : module_in_package
module module_generate (
  input bit [3:0] in_gen_sel,
  output logic [3:0] out_gen_val
);
  public parameter int GEN_OFFSET = 1;
  logic [3:0] gen_internal_val [4];
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_block
      always_comb begin
        gen_internal_val[i] = in_gen_sel + i + GEN_OFFSET;
      end
    end
  endgenerate
  assign out_gen_val = gen_internal_val[in_gen_sel % 4];
endmodule : module_generate
(* keep_hierarchy *)
module module_nested (
  input bit in_nested,
  output bit out_nested
);
  logic basic_in;
  logic basic_out;
  module_basic basic_inst (
    .in_basic(basic_in),
    .out_basic(basic_out)
  );
  assign basic_in = in_nested;
  assign out_nested = basic_out;
endmodule : module_nested
module module_public_param #(
  public parameter int PUBLIC_COUNT = 5
) (
  input int in_pub_param,
  output int out_pub_param
);
  assign out_pub_param = in_pub_param * PUBLIC_COUNT;
endmodule : module_public_param
module module_package_access (
  input bit clk_in,
  input int in_pkg_val,
  output int out_pkg_val
);
  import my_package::*;
  MyPackageClass pkg_class_h;
  always @(posedge clk_in) begin
    if (pkg_class_h == null) begin
      pkg_class_h = new();
    end
    if (pkg_class_h != null) begin
      pkg_class_h.setVal(in_pkg_val + package_public_int + PACKAGE_PUBLIC_PARAM);
    end
  end
  assign out_pkg_val = (pkg_class_h != null) ? pkg_class_h.class_val_in_pkg : 0;
endmodule : module_package_access

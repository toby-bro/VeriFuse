package my_verilator_pkg;
  class PkgClassA;
    static logic [7:0] static_prop_a (* verilator trace *) = 8'hAA;
    logic [7:0] inst_prop_a (* verilator trace *) = 8'h11;
    function new();
      this.inst_prop_a = 8'hCD;
    endfunction
    function new(PkgClassA source);
      this.inst_prop_a = source.inst_prop_a;
    endfunction
    function logic [7:0] get_prop();
      return this.inst_prop_a;
    endfunction
  endclass
  class PkgClassB;
    static int static_prop_b (* verilator trace *) = 100;
    int inst_prop_b (* verilator trace *) = 200;
    function new(int val);
      this.inst_prop_b = val;
    endfunction
  endclass
  typedef enum {
    PKG_STATE_IDLE = 2'b00,
    PKG_STATE_BUSY = 2'b01,
    PKG_STATE_DONE = 2'b10
  } PkgState_e (* verilator trace *);
  typedef struct { logic [7:0] field_up1; int field_up2; } PkgUnpackedStruct_t (* verilator trace *);
endpackage
import my_verilator_pkg::*;
module ModulePackageClassAccess (
  input logic dummy_pkg_in,
  output logic [7:0] out_static_prop_a (* verilator public, verilator trace *),
  output int out_static_prop_b (* verilator public, verilator trace *),
  output PkgState_e out_pkg_enum (* verilator public, verilator trace *)
) (* verilator savable *);
  always_comb begin
    out_static_prop_a = my_verilator_pkg::PkgClassA::static_prop_a ^ {8{dummy_pkg_in}};
    out_static_prop_b = my_verilator_pkg::PkgClassB::static_prop_b + (dummy_pkg_in ? 1 : 0);
    out_pkg_enum = dummy_pkg_in ? PKG_STATE_BUSY : PKG_STATE_IDLE;
  end
endmodule
module ModuleArithmeticLogicControl (
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  input bit in_sel,
  input [2:0] in_case_sel,
  input [3:0] in_loop_iter,
  output logic [7:0] out_result_ops (* verilator public, verilator trace *),
  output logic [7:0] out_result_ctrl (* verilator public, verilator trace *),
  output logic [7:0] out_result_loop (* verilator public, verilator trace *),
  output logic [15:0] out_concat_slice (* verilator public, verilator trace *)
) (* verilator savable *);
  parameter PARAM_ADD = 5;
  logic [7:0] internal_ops (* verilator trace *);
  logic [7:0] internal_ctrl (* verilator trace *);
  logic [7:0] internal_loop (* verilator trace *);
  always_comb begin
    internal_ops = (in_a + in_b) - PARAM_ADD;
    internal_ops = internal_ops & (~in_a | in_b);
    internal_ops = (internal_ops << 1) ^ (internal_ops >> 1);
    internal_ops = {8{^internal_ops}};
    out_result_ops = internal_ops;
    out_concat_slice = {in_a, in_b}[15:0];
    if (in_sel) begin
      internal_ctrl = in_a;
    end else begin
      internal_ctrl = in_b;
    end
    case (in_case_sel)
      3'd0: internal_ctrl = internal_ctrl + 1;
      3'd1: internal_ctrl = internal_ctrl - 1;
      default: internal_ctrl = 8'hFF;
    endcase
    out_result_ctrl = internal_ctrl;
    internal_loop = 8'b0;
    for (int i = 0; i < in_loop_iter; i++) begin
      if (i < 8) internal_loop[i] = in_a[i] ^ in_b[i];
    end
    out_result_loop = internal_loop;
  end
endmodule
module ModuleDataStructures (
  input logic [31:0] in_data,
  input logic [1:0] in_enum_sel,
  input int in_array_idx,
  output logic [15:0] out_struct_val (* verilator public, verilator trace *),
  output logic [3:0] out_enum_val (* verilator public, verilator trace *),
  output logic [7:0] out_typedef_val (* verilator public, verilator trace *),
  output logic [7:0] out_unpacked_array_val (* verilator public, verilator trace *),
  output logic [7:0] out_packed_array_val (* verilator public, verilator trace *),
  output logic [7:0] out_unpacked_vec_array_val (* verilator public, verilator trace *)
) (* verilator savable *);
  typedef struct packed {
    logic [7:0] field1;
    logic [7:0] field2;
  } MyPackedStruct_t;
  typedef struct {
    logic [7:0] field_u1;
    logic [7:0] field_u2;
  } MyUnpackedStruct_t;
  typedef enum {
    STATE_A = 4'hA,
    STATE_B = 4'hB,
    STATE_C = 4'hC
  } MyState_e (* verilator trace *);
  typedef logic [7:0] byte_t;
  MyPackedStruct_t internal_packed_struct (* verilator trace *);
  MyState_e current_enum_state (* verilator trace *);
  byte_t internal_typedef_byte (* verilator trace *);
  logic [7:0] internal_unpacked_array [0:3] (* verilator trace *);
  logic [3:0][7:0] internal_packed_array (* verilator trace *);
  logic [7:0] internal_unpacked_vec_array [0:3] (* verilator trace *);
  always_comb begin
    internal_packed_struct.field1 = in_data[7:0];
    internal_packed_struct.field2 = in_data[15:8];
    out_struct_val = internal_packed_struct.field1 + internal_packed_struct.field2;
    case (in_enum_sel)
      2'b00: current_enum_state = STATE_A;
      2'b01: current_enum_state = STATE_B;
      default: current_enum_state = STATE_C;
    endcase
    out_enum_val = current_enum_state;
    internal_typedef_byte = in_data[7:0];
    out_typedef_val = internal_typedef_byte;
    for(int i=0; i<4; i++) begin
      internal_unpacked_array[i] = in_data[i*8 +: 8] + 1;
      internal_packed_array[i] = in_data[i*8 +: 8] + 2;
      internal_unpacked_vec_array[i] = in_data[i*8 +: 8] + 3;
    end
    if (in_array_idx >= 0 && in_array_idx < 4) begin
      out_unpacked_array_val = internal_unpacked_array[in_array_idx];
      out_packed_array_val = internal_packed_array[in_array_idx];
      out_unpacked_vec_array_val = internal_unpacked_vec_array[in_array_idx];
    end else begin
      out_unpacked_array_val = 8'h00;
      out_packed_array_val = 8'h00;
      out_unpacked_vec_array_val = 8'h00;
    end
  end
endmodule
module ModuleClasses (
  input logic in_trigger,
  input logic [7:0] in_val,
  input logic in_op_sel,
  output logic out_op_done (* verilator public, verilator trace *),
  output logic [7:0] out_method_result (* verilator public, verilator trace *),
  output logic [7:0] out_copied_result (* verilator public, verilator trace *)
) (* verilator savable, verilator sc_implementation *);
  class MyClassProc;
    logic [7:0] prop_proc (* verilator trace *) = 8'hDE;
    function new(); this.prop_proc = 8'hEF; endfunction
    function new(MyClassProc source); this.prop_proc = source.prop_proc; endfunction
    function logic [7:0] method_op(logic [7:0] data, bit sel);
      if (sel) return this.prop_proc + data;
      else return this.prop_proc - data;
    endfunction
    function logic [7:0] get_prop();
      return this.prop_proc;
    endfunction
  endclass
  logic [7:0] internal_method_res (* verilator trace *);
  logic [7:0] internal_copy_res (* verilator trace *);
  logic internal_op_flag (* verilator trace *) = 1'b0;
  task automatic perform_class_ops(logic [7:0] data, bit op);
    MyClassProc inst_a;
    MyClassProc inst_b;
    inst_a = new();
    internal_method_res = inst_a.method_op(data, op);
    inst_b = new(inst_a);
    internal_copy_res = inst_b.get_prop();
    internal_op_flag = 1'b1;
  endtask
  always_comb begin
    out_op_done = internal_op_flag;
    out_method_result = internal_method_res;
    out_copied_result = internal_copy_res;
    if (in_trigger) begin
      perform_class_ops(in_val, in_op_sel);
    end else begin
      internal_op_flag = 1'b0;
      internal_method_res = 8'h00;
      internal_copy_res = 8'h00;
    end
  end
endmodule
module ModuleSystemC (
  input logic dummy_sc_in,
  input sc_uint #(8) in_sc_uint (* verilator trace *),
  input sc_bv #(32) in_sc_bv (* verilator trace *),
  input sc_bigint <64> in_sc_bigint (* verilator trace *),
  input sc_biguint <128> in_sc_biguint (* verilator trace *),
  output sc_uint #(8) out_sc_uint (* verilator public, verilator trace *),
  output sc_bv #(32) out_sc_bv (* verilator public, verilator trace *),
  output sc_bigint <64> out_sc_bigint (* verilator public, verilator trace *),
  output sc_biguint <128> out_sc_biguint (* verilator public, verilator trace *),
  output logic out_dummy_sc (* verilator public, verilator trace *)
) (* verilator sc_interface, verilator savable *);
  always_comb begin
    out_dummy_sc = dummy_sc_in;
    out_sc_uint = in_sc_uint + 1;
    out_sc_bv = ~in_sc_bv;
    out_sc_bigint = in_sc_bigint + 1;
    out_sc_biguint = in_sc_biguint + 1;
  end
endmodule
module ModuleCoverageDPI (
  input logic [1:0] in_cov_sig,
  input int in_dpi_arg,
  input logic in_dump_trigger,
  output logic [1:0] out_cov_sig (* verilator public, verilator trace *),
  output int out_dpi_result (* verilator public, verilator trace *),
  output bit out_dump_triggered (* verilator public, verilator trace *)
) (* verilator savable *);
  covergroup MyCovergroup (* auto_bin_max=0 *) @(out_cov_sig);
    cp_sig : coverpoint out_cov_sig {
      bins b0 = {0};
      bins b1 = {1};
      bins b2 = {2};
      bins b3 = {3};
    }
  endgroup
  MyCovergroup my_cg (* verilator trace *);
  import "C" function int my_dpi_function(int arg);
  int internal_dpi_result (* verilator trace *);
  logic internal_dump_flag = 1'b0;
  task automatic call_dpi_and_cover(int arg);
    internal_dpi_result = my_dpi_function(arg);
    my_cg.sample();
    if (in_dump_trigger) begin
        internal_dump_flag = 1'b1;
    end
  endtask
  always_comb begin
    out_cov_sig = in_cov_sig;
    out_dpi_result = internal_dpi_result;
    out_dump_triggered = internal_dump_flag;
    call_dpi_and_cover(in_dpi_arg);
  end
endmodule
module ModuleTextSavable (
  input logic in_sel,
  output logic out_dummy (* verilator public, verilator trace *)
) (* verilator sc_implementation, verilator savable *);
  logic internal_flag (* verilator trace *);
  string internal_string (* verilator trace *) = "This string contains vlSymsp and other text.";
  always_comb begin
    internal_flag = in_sel;
    out_dummy = internal_flag;
  end
  systemc_implementation {{
    int text_impl_var VL_ATTR_UNUSED = 0;
    const char* text_impl_string VL_ATTR_UNUSED = "Some systemc_implementation text potentially referencing vlSymsp";
    if (text_impl_var == 0) { }
    if (text_impl_string[0] == 'S') { }
  }}
endmodule
module ModuleInout (
  input logic in_ctrl,
  inout logic io_port (* verilator public, verilator trace *),
  output logic out_port_read (* verilator public, verilator trace *),
  output logic out_port_driven (* verilator public, verilator trace *)
) (* verilator savable *);
  logic driver_en (* verilator trace *);
  logic driver_data (* verilator trace *);
  assign io_port = driver_en ? driver_data : 'z;
  always_comb begin
    if (in_ctrl) begin
      driver_en = 1'b1;
      driver_data = 1'b1;
    end else begin
      driver_en = 1'b0;
      driver_data = 1'b0;
    end
    out_port_read = io_port;
    out_port_driven = driver_data;
  end
endmodule
module ModuleScope (
  input logic in_trigger,
  output logic out_scoped_flag (* verilator public, verilator trace *)
) (* verilator savable *);
  logic internal_scoped_flag (* verilator trace *) = 1'b0;
  always_comb begin : my_scoped_block
    if (in_trigger) begin
      use_scope_task;
    end else begin
      internal_scoped_flag = 1'b0;
    end
    out_scoped_flag = internal_scoped_flag;
  end
  task automatic use_scope_task;
    internal_scoped_flag = 1'b1;
  endtask
endmodule
module ModuleLiteralTypes (
    input bit in_bit,
    input byte in_byte,
    input shortint in_shortint,
    input int in_int,
    input longint in_longint,
    input integer in_integer,
    input time in_time,
    input real in_real,
    input shortreal in_shortreal,
    input double in_double,
    input string in_string,
    output bit out_bit (* verilator public, verilator trace *),
    output byte out_byte (* verilator public, verilator trace *),
    output shortint out_shortint (* verilator public, verilator trace *),
    output int out_int (* verilator public, verilator trace *),
    output longint out_longint (* verilator public, verilator trace *),
    output integer out_integer (* verilator public, verilator trace *),
    output time out_time (* verilator public, verilator trace *),
    output real out_real (* verilator public, verilator trace *),
    output shortreal out_shortreal (* verilator public, verilator trace *),
    output double out_double (* verilator public, verilator trace *),
    output string out_string (* verilator public, verilator trace *)
) (* verilator savable *);
    always_comb begin
        out_bit = in_bit;
        out_byte = in_byte;
        out_shortint = in_shortint;
        out_int = in_int;
        out_longint = in_longint;
        out_integer = in_integer;
        out_time = in_time;
        out_real = in_real;
        out_shortreal = in_shortreal;
        out_double = in_double;
        out_string = in_string;
    end
endmodule
module ModuleMTaskState (
  input logic in_trigger_m,
  output logic out_state_nonzero (* verilator public, verilator trace *),
  output logic [1:0] out_mtask_state (* verilator public, verilator trace *)
) (* verilator savable *);
  logic [1:0] mtask_state (* verilator trace, verilator_state_machine * ) = 2'b0;
  always_comb begin
    if (in_trigger_m) begin
      mtask_state = mtask_state + 1;
    end else begin
      mtask_state = 2'b0;
    end
    out_state_nonzero = (mtask_state != 2'b0);
    out_mtask_state = mtask_state;
  end
endmodule
module ModuleAdvancedStructures (
  input logic in_trigger_adv,
  input int in_aa_idx,
  input logic [7:0] in_queue_data,
  input logic in_union_sel,
  output logic out_adv_op_done (* verilator public, verilator trace *),
  output logic [7:0] out_aa_val (* verilator public, verilator trace *),
  output logic [7:0] out_queue_val (* verilator public, verilator trace *),
  output logic [15:0] out_union_val (* verilator public, verilator trace *)
) (* verilator savable *);
  logic [7:0] aa_var [*];
  logic [7:0] queue_var [$];
  typedef union {
    logic [7:0] byte_field;
    logic [15:0] short_field;
  } MyUnion_t;
  MyUnion_t union_var (* verilator trace *);
  logic out_adv_flag (* verilator trace *) = 1'b0;
  logic [7:0] internal_aa_val (* verilator trace *);
  logic [7:0] internal_queue_val (* verilator trace *);
  logic [15:0] internal_union_val (* verilator trace *);
  task automatic process_advanced_structures(int aa_idx, logic [7:0] q_data, logic u_sel);
    if (aa_var.exists(aa_idx)) begin
      internal_aa_val = aa_var[aa_idx];
    end else begin
      aa_var[aa_idx] = aa_idx + 10;
      internal_aa_val = aa_var[aa_idx];
    end
    queue_var.push_back(q_data);
    if (queue_var.size() > 0) begin
        internal_queue_val = queue_var[0];
    end else begin
        internal_queue_val = 8'h00;
    end
    if (u_sel) begin
        union_var.short_field = {8'hAA, 8'hBB};
    end else begin
        union_var.byte_field = 8'hCC;
    end
    internal_union_val = union_var.short_field;
    out_adv_flag = 1'b1;
  endtask
  always_comb begin
    out_aa_val = internal_aa_val;
    out_queue_val = internal_queue_val;
    out_union_val = internal_union_val;
    out_adv_op_done = out_adv_flag;
    if (in_trigger_adv) begin
      process_advanced_structures(in_aa_idx, in_queue_data, in_union_sel);
    end else begin
       out_adv_flag = 1'b0;
       internal_aa_val = 8'h00;
       internal_queue_val = 8'h00;
       internal_union_val = 16'h0000;
    end
  end
endmodule
module ModuleTimeTasks (
  input logic in_trigger_time,
  output logic out_time_op_done (* verilator public, verilator trace *)
) (* verilator savable, verilator trace *);
  logic time_ops_done = 1'b0;
  task automatic do_time_ops;
    time_ops_done = 1'b1;
  endtask
  always_comb begin
    out_time_op_done = time_ops_done;
    if (in_trigger_time) begin
      do_time_ops;
    end else begin
      time_ops_done = 1'b0;
    end
  end
endmodule
module ModuleTimePrintTasks (
  input logic in_trigger_time_print,
  input int in_units,
  input int in_precision,
  output time out_current_time (* verilator public, verilator trace *)
) (* verilator savable, verilator trace *);
  logic trigger_internal = in_trigger_time_print;
  time internal_time (* verilator trace *);
  always_comb begin
    if (trigger_internal) begin
      $timeformat(in_units, in_precision, "ps", ".");
      $printtimescale;
      $printtimescale(".");
      internal_time = $realtime;
    end else begin
       internal_time = 0;
    end
    out_current_time = internal_time;
  end
endmodule
module ModuleDumpCtl (
  input logic in_trigger_dump,
  input int in_dump_level,
  output bit out_dump_triggered (* verilator public, verilator trace *),
  output int out_dummy_dump (* verilator public, verilator trace *)
) (* verilator savable, verilator trace *);
  logic internal_dump_flag = 1'b0;
  int internal_dummy = 0;
  task automatic do_dump_calls;
    $dumpfile("vlt_dump.vcd");
    $dumpvars(in_dump_level);
    $dumpoff;
    $dumpon;
    internal_dump_flag = 1'b1;
  endtask
  always_comb begin
    out_dump_triggered = internal_dump_flag;
    out_dummy_dump = internal_dummy;
    if (in_trigger_dump) begin
      do_dump_calls;
    end else begin
      internal_dump_flag = 1'b0;
    end
  end
endmodule
module ModuleModuleClass (
  input logic in_class_trigger,
  input logic [7:0] in_class_val,
  output logic [7:0] out_class_prop (* verilator public, verilator trace *),
  output logic [7:0] out_class_op_result (* verilator public, verilator trace *)
) (* verilator savable *);
  class MyModuleLocalClass;
    logic [7:0] prop_local (* verilator trace *) = 8'h10;
    function new(); this.prop_local = 8'h20; endfunction
    function logic [7:0] method_add(logic [7:0] data);
      return this.prop_local + data;
    endfunction
  endclass
  logic [7:0] internal_prop (* verilator trace *);
  logic [7:0] internal_result (* verilator trace *);
  task automatic use_local_class(logic [7:0] val);
    MyModuleLocalClass local_inst;
    local_inst = new();
    internal_prop = local_inst.prop_local;
    internal_result = local_inst.method_add(val);
  endtask
  always_comb begin
    out_class_prop = internal_prop;
    out_class_op_result = internal_result;
    if (in_class_trigger) begin
      use_local_class(in_class_val);
    end else begin
      internal_prop = 8'h00;
      internal_result = 8'h00;
    end
  end
endmodule
module ModuleModuleTypedefs (
  input logic [15:0] in_typedef_data,
  output logic [7:0] out_typedef_struct_val (* verilator public, verilator trace *),
  output logic [15:0] out_typedef_union_val (* verilator public, verilator trace *)
) (* verilator savable *);
  typedef struct packed {
    logic [7:0] ts_f1;
    logic [7:0] ts_f2;
  } ModuleStruct_t;
  typedef union {
    logic [7:0] tu_byte;
    logic [15:0] tu_short;
  } ModuleUnion_t;
  ModuleStruct_t internal_m_struct (* verilator trace *);
  ModuleUnion_t internal_m_union (* verilator trace *);
  always_comb begin
    internal_m_struct.ts_f1 = in_typedef_data[7:0];
    internal_m_struct.ts_f2 = in_typedef_data[15:8];
    out_typedef_struct_val = internal_m_struct.ts_f1 + internal_m_struct.ts_f2;
    internal_m_union.tu_short = in_typedef_data;
    out_typedef_union_val = internal_m_union.tu_short;
  end
endmodule
module ModuleNestedStructures (
  input int in_nested_idx,
  input logic in_nested_union_sel,
  input logic [23:0] in_nested_data,
  output logic [7:0] out_array_of_struct (* verilator public, verilator trace *),
  output logic [15:0] out_struct_with_union (* verilator public, verilator trace *),
  output logic [7:0] out_struct_with_array (* verilator public, verilator trace *)
) (* verilator savable *);
  typedef struct packed {
    logic [3:0] ns_f1;
    logic [3:0] ns_f2;
  } SimpleStruct_t;
  SimpleStruct_t array_of_structs [0:3] (* verilator trace *);
  typedef struct packed {
    logic [7:0] swu_field;
    union packed {
      logic [7:0] swu_byte;
      logic [15:0] swu_short;
    } swu_union;
  } StructWithUnion_t;
  StructWithUnion_t internal_swu (* verilator trace *);
  typedef struct packed {
      logic [7:0] swa_array [0:2];
  } StructWithArray_t;
  StructWithArray_t internal_swa (* verilator trace *);
  always_comb begin
    for (int i = 0; i < 4; i++) begin
      array_of_structs[i].ns_f1 = in_nested_data[i*8 +: 4];
      array_of_structs[i].ns_f2 = in_nested_data[i*8 + 4 +: 4];
    end
    if (in_nested_idx >= 0 && in_nested_idx < 4) begin
      out_array_of_struct = {array_of_structs[in_nested_idx].ns_f1, array_of_structs[in_nested_idx].ns_f2};
    end else begin
      out_array_of_struct = 8'h00;
    end
    internal_swu.swu_field = in_nested_data[7:0];
    if (in_nested_union_sel) begin
        internal_swu.swu_union.swu_short = in_nested_data[23:8];
    end else begin
        internal_swu.swu_union.swu_byte = in_nested_data[15:8];
    end
    out_struct_with_union = {internal_swu.swu_field, internal_swu.swu_union.swu_byte};
    for (int i = 0; i < 3; i++) begin
        internal_swa.swa_array[i] = in_nested_data[i*8 +: 8];
    end
    if (in_nested_idx >= 0 && in_nested_idx < 3) begin
        out_struct_with_array = internal_swa.swa_array[in_nested_idx];
    end else begin
        out_struct_with_array = 8'h00;
    end
  end
endmodule
module ModuleChild (
  input logic in_child,
  output logic out_child (* verilator public, verilator trace *)
) (* verilator savable *);
  assign out_child = ~in_child;
endmodule
module ModuleParent (
  input logic in_parent_ctrl,
  output logic out_parent (* verilator public, verilator trace *)
) (* verilator savable *);
  logic parent_internal_sig (* verilator trace *);
  logic child_output (* verilator trace *);
  ModuleChild child_inst (
    .in_child(in_parent_ctrl),
    .out_child(child_output)
  );
  always_comb begin
    parent_internal_sig = in_parent_ctrl & child_output;
    out_parent = parent_internal_sig;
  end
endmodule
module ModuleUsesPackageUnpackedStruct (
  input logic [15:0] in_up_data,
  output int out_up_sum (* verilator public, verilator trace *)
) (* verilator savable *);
  PkgUnpackedStruct_t internal_up_struct (* verilator trace *);
  always_comb begin
    internal_up_struct.field_up1 = in_up_data[7:0];
    internal_up_struct.field_up2 = in_up_data[15:8];
    out_up_sum = internal_up_struct.field_up1 + internal_up_struct.field_up2;
  end
endmodule
module ModuleUsesPackageClass (
  input logic in_pc_trigger,
  input logic [7:0] in_pc_val,
  output logic [7:0] out_pc_prop (* verilator public, verilator trace *)
) (* verilator savable *);
  PkgClassA internal_pc_inst (* verilator trace *);
  logic [7:0] internal_pc_prop (* verilator trace *) = 8'h00;
  task automatic process_package_class(logic [7:0] val);
    internal_pc_inst = new();
    internal_pc_inst.inst_prop_a = val;
    internal_pc_prop = internal_pc_inst.get_prop();
  endtask
  always_comb begin
    out_pc_prop = internal_pc_prop;
    if (in_pc_trigger) begin
      process_package_class(in_pc_val);
    end else begin
      internal_pc_prop = 8'h00;
    end
  end
endmodule

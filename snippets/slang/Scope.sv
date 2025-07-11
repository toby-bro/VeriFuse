package user_defined_net_pkg;
  nettype logic my_ud_wire;
endpackage
package pkg_data_types;
  parameter int PKG_PARAM = 50;
  logic [15:0] pkg_var_in_pkg = 16'hABCD;
  typedef enum { RED, GREEN, BLUE } color_e;
  color_e default_color = RED;
  typedef struct packed {
    bit enable;
    int count;
  } packed_struct_t;
  class another_class;
    int data;
    function new();
      data = 0;
    endfunction
  endclass
  typedef class another_class;
  function automatic int get_pkg_param();
    return PKG_PARAM;
  endfunction
  task set_pkg_var(logic [15:0] val);
    pkg_var_in_pkg = val;
  endtask
endpackage
class my_class;
  int value;
  function new();
    value = 0;
  endfunction
endclass
class base_class;
  int base_val;
  function new(int v);
    base_val = v;
  endfunction
  function int get_base_val();
    return base_val;
  endfunction
endclass
class derived_class extends base_class;
  int derived_val;
  function new(int v1, int v2);
    super.new(v1);
    derived_val = v2;
  endfunction
  function int get_derived_val();
    return derived_val;
  endfunction
endclass
module module_with_param (
  input  logic in,
  output logic named_out
);
  parameter int DELAY = 10;
  logic bind_dummy_in;
  logic bind_dummy_out;
  assign named_out = in;
endmodule
module bind_module (
  input  logic bind_in,
  output logic bind_out
);
  assign bind_out = bind_in;
endmodule
interface intf_timing (
  input  bit  clk,
  input  logic enable
);
  wire data;
  logic other_sig;
  clocking cb @(posedge clk);
    input data;
    input enable;
  endclocking
  modport mp_master (
    input  clk,
    input  enable,
    inout  data,
    clocking cb,
    import function int get_value(int x),
    export task set_value(int y)
  );
  default clocking cb;
  function int get_value(int x);
    return x * 2;
  endfunction
  task set_value(int y);
  endtask
endinterface
interface intf_implicit_port;
  wire data;
endinterface
module mod_implicit_interface_port (
  input  bit  clk,
  output logic [3:0] out_data
);
  intf_implicit_port implicit_intf ();
  assign out_data = implicit_intf.data;
endmodule
checker simple_checker (
  input bit clk,
  input bit sig
);
  logic [7:0] count;
  always_ff @(posedge clk) count <= count + 1;
  property p1; @(posedge clk) sig |-> !sig; endproperty
  a_p1: assert property (p1);
  property p_count_nonzero;
    @(posedge clk) count != 0;
  endproperty
  a_p_count_nonzero: assert property (@(posedge clk) p_count_nonzero);
endchecker
module mod_basic_logic (
  input  logic clk,
  input  logic reset,
  output wire [7:0] data_out
);
  localparam int MAX_COUNT   = 100;
  parameter   int START_VALUE = 5;
  logic [7:0] internal_reg;
  int         counter;
  real        current_temp;
  typedef enum { IDLE, RUNNING, DONE } state_e;
  state_e current_state;
  typedef struct {
    int   value;
    logic enable;
  } data_struct_t;
  data_struct_t my_data;
  my_class inst;
  assign data_out = internal_reg + START_VALUE;
  always_comb begin
    if (current_state == IDLE) begin
      my_data.enable = 1;
      current_temp = 25.0;
    end else begin
      my_data.enable = 0;
      current_temp = 75.0;
    end
  end
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      internal_reg  <= 0;
      counter       <= 0;
      current_state <= IDLE;
    end else begin
      if (counter < MAX_COUNT) begin
        internal_reg  <= internal_reg + 1;
        counter       <= counter + 1;
        current_state <= RUNNING;
      end else begin
        internal_state_task(internal_reg);
        current_state <= DONE;
      end
    end
  end
  initial begin
    my_data.value = initial_value_func(START_VALUE);
    inst = new();
  end
  function int initial_value_func(int start);
    return start * 2;
  endfunction
  task internal_state_task(logic [7:0] current_data);
  endtask
endmodule
module mod_hierarchy_generates (
  input  logic       clk,
  input  logic       reset,
  input  logic [3:0] selector_in,
  input  logic       enable_genvar,
  output wire  [7:0] generated_output,
  output wire  [7:0] instantiated_output
);
  parameter int NUM_INST    = 2;
  parameter int GEN_SELECT  = 0;
  module nested_module (input bit dummy_in, output bit dummy_out);
    assign dummy_out = dummy_in;
  endmodule
  wire dummy_and_out;
  wire dummy_xor_out;
  and a1 (dummy_and_out, enable_genvar, selector_in[0]);
  xor x1 (dummy_xor_out, enable_genvar, selector_in[1]);
  assign instantiated_output[0] = dummy_and_out;
  assign instantiated_output[1] = dummy_xor_out;
  simple_checker checker_inst ( .clk(clk), .sig(enable_genvar) );
  if (NUM_INST == 2) begin : gen_if_two_inst
    assign generated_output[0] = selector_in[2];
  end else begin : gen_if_not_two_inst
    assign generated_output[0] = selector_in[3];
  end
  case (GEN_SELECT)
    0: begin : gen_case_00
      assign generated_output[1] = selector_in[0];
    end
    1: begin : gen_case_01
      assign generated_output[1] = selector_in[1];
    end
    default: begin : gen_case_default
      assign generated_output[1] = selector_in[2];
    end
  endcase
  genvar i;
  for (i = 0; i < NUM_INST; i++) begin : gen_loop_inst
    begin : loop_block
      int   loop_var;
      logic [7:0] block_local_logic;
      always_comb begin
        loop_var           = i + 1;
        block_local_logic  = loop_var;
      end
    end
    mod_basic_logic child_inst (
      .clk   (clk),
      .reset (reset),
      .data_out(instantiated_output[i*4+:4])
    );
  end
  module another_nested_module (input logic i, output logic o);
    assign o = i;
  endmodule
  wire [7:0] output_part_alias;
  alias output_part_alias = instantiated_output[7:0];
  assign generated_output[7:4] = output_part_alias[7:4];
endmodule
module mod_verification (
  input  bit clk,
  input  bit enable,
  input  int value_in,
  output bit success
);
  class verification_item;
    rand int addr;
    rand int data;
    local int id = 1;
    constraint c_addr { addr inside {[0:100]}; }
    constraint c_data { data > 0; }
    function new();
    endfunction
    function void print_item();
    endfunction
  endclass
  sequence s_enable;
    @(posedge clk) enable;
  endsequence
  property p_value_stable;
    @(posedge clk) enable |-> $stable(value_in);
  endproperty
  a_p_value_stable: assert property (p_value_stable);
  always_comb begin
    if (enable)
      assert(value_in > 0);
  end
  initial begin
    static verification_item item = new();
    success = 1'b1;
  end
  covergroup value_cg @(posedge clk);
    option.per_instance = 1;
    value_cp : coverpoint value_in {
      bins zero_bin      = {0};
      bins small_range[] = {[1:10]};
      bins large_bins    = {100, 200};
      illegal_bins negative_bins = {[-10:-1]};
      ignore_bins  unused_bins   = {999};
      bins other_values_bins = default;
    }
    enable_cp : coverpoint enable {
      bins on  = {1};
      bins off = {0};
    }
    value_enable_cross : cross value_cp, enable_cp {
      bins cross_all = binsof(value_cp) && binsof(enable_cp);
    }
  endgroup
  value_cg cg_inst = new();
endmodule
module mod_connectivity_timing (
  input  bit   clk,
  input  logic non_ansi_in,
  output wire  non_ansi_out
);
  wire        normal_wire;
  reg         normal_reg;
  wand        normal_wand;
  wor         normal_wor;
  tri         normal_tri;
  wire  [7:0] alias_target;
  wire        normal_wire_alias_bit;
  alias normal_wire_alias_bit = alias_target[0];
  assign normal_wire = normal_wire_alias_bit;
  module_with_param param_inst (
    .in       (non_ansi_in),
    .named_out(non_ansi_out)
  );
  wire ambiguous_in_dummy;
  wire ambiguous_out_dummy;
  module_with_param ambiguous_inst (
    .in       (ambiguous_in_dummy),
    .named_out(ambiguous_out_dummy)
  );
  defparam param_inst.DELAY = 20;
  bind param_inst bind_module bind_inst (
    .bind_in (param_inst.bind_dummy_in),
    .bind_out(param_inst.bind_dummy_out)
  );
  intf_timing timing_intf (.clk(clk), .enable(non_ansi_in));
  assign non_ansi_out = timing_intf.data;
endmodule
module mod_using_package (
  input  logic [7:0] input_val,
  output logic [7:0] output_val
);
  import pkg_data_types::PKG_PARAM;
  import pkg_data_types::pkg_var_in_pkg;
  import pkg_data_types::*;
  logic [15:0] module_pkg_var_local = 16'h5678;
  typedef enum { A, B } local_color_e;
  pkg_data_types::color_e current_color = pkg_data_types::RED;
  localparam int MODULE_PARAM = PKG_PARAM * 2;
  int pkg_param_val = get_pkg_param();
  assign output_val = input_val + module_pkg_var_local[7:0];
  import user_defined_net_pkg::my_ud_wire;
  my_ud_wire udt_net;
  wire [7:0] wired_val;
  assign wired_val = input_val + 1;
  assign udt_net = wired_val[0];
endmodule
module mod_default_disable (
  input bit enable_in,
  output bit out
);
  assign out = enable_in;
endmodule
module buf_primitive (
  input  wire i,
  output wire o
);
  buf b1 (o, i);
endmodule
module mod_unused_ports (
  input  wire  unused_in,
  output logic unused_out
);
  assign unused_out = unused_in;
endmodule
module mod_specify (
  input  wire i_in_bit,
  input  wire j_in_bit,
  output wire o_out_bit
);
  specparam sp_delay = 10;
  specify
    (i_in_bit => o_out_bit) = sp_delay;
    $setup(i_in_bit, j_in_bit, 5);
  endspecify
  assign o_out_bit = i_in_bit ^ j_in_bit;
endmodule
module mod_name_conflict (
  input  logic in_a,
  output logic out_a
);
  logic conflict_var;
  parameter int conflict_param = 1;
  assign out_a = in_a;
endmodule
module mod_import_conflict (
  input  logic in_b,
  output logic out_b
);
  import pkg_data_types::PKG_PARAM;
  import pkg_data_types::PKG_PARAM;
  assign out_b = in_b;
endmodule
module mod_statement_block_var (
  input  logic in_c,
  output logic out_c
);
  always_comb begin : block_with_vars
    int   block_local_int;
    logic [7:0] block_local_logic;
    block_local_int   = in_c ? 10 : 20;
    block_local_logic = block_local_int;
    out_c             = block_local_logic[0];
  end
endmodule
module mod_class_inheritance (
  input  int input_val,
  output int output_val
);
  derived_class derived_inst;
  initial begin
    derived_inst = new(input_val, input_val * 2);
  end
  always_comb begin
    output_val = derived_inst.get_base_val() + derived_inst.get_derived_val();
  end
endmodule
module mod_let_declaration (
  input  int in_val,
  output int out_val
);
  let my_let_expr = in_val + 5;
  assign out_val = my_let_expr * 2;
endmodule
module mod_constraint_block (
  input  int input_data,
  output bit constraint_ok
);
  always_comb begin
    if (input_data >= 0 && input_data <= 10)
      constraint_ok = 1;
    else
      constraint_ok = 0;
  end
  assert (input_data != 42);
endmodule

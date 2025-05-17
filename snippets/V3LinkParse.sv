primitive my_udp (out, in1, in2);
  output out;
  input in1, in2;
  table
     0   0  : 0;
     0   1  : 1;
     1   0  : 1;
     1   1  : 0;
     x   ?  : x;
     ?   x  : x;
  endtable
endprimitive
package my_package;
  parameter PKG_PARAM = 7;
  class PkgClass;
    int pkg_val = 10;
    function new();
      pkg_val = 20;
    endfunction
    function automatic int get_pkg_val();
      return pkg_val;
    endfunction
  endclass
endpackage
class BaseClass;
  int base_val;
  function new();
    base_val = 1;
  endfunction
endclass
class DerivedClass extends BaseClass;
  int derived_val;
  function new();
    super.new();
    derived_val = 0;
    derived_val = 2;
  endfunction
  function int get_total();
    return base_val + derived_val;
  endfunction
endclass
class DerivedClassSuperNewError extends BaseClass;
  int derived_val;
  function new();
    derived_val = 0;
    super.new();
    derived_val = 2;
  endfunction
endclass
class ClassWithConstraint;
  rand int val;
  constraint val_range { val inside {[1:10]}; }
  function new(); endfunction
endclass
class ClassWithImportError;
  import my_package::*;
  int imported_val = 0;
  function new();
    imported_val = PKG_PARAM;
  endfunction
  function int get_val();
    return imported_val;
  endfunction
endclass
module ModuleTaskFunc (input wire i_clk, output logic o_done);
  logic [7:0] data;
  static int module_static_var = 99;
  automatic int module_automatic_var;
  int module_implicit_static_var_init = 10;
  function automatic int simple_func (input int val);
    int func_local_automatic_var_init = 5;
    static int func_local_static_var_no_init;
    func_local_static_var_no_init = func_local_static_var_no_init + 1;
    return val + 1 + func_local_automatic_var_init + func_local_static_var_no_init;
  endfunction
  task static simple_task (input int val, output logic [7:0] result);
    int task_local_implicit_static_var_init = 1;
    static int task_local_static_var_no_init;
    task_local_static_var_no_init = task_local_static_var_no_init + 1;
    result = val * 2 + task_local_implicit_static_var_init + task_local_static_var_no_init;
  endtask
  always_ff @(posedge i_clk) begin
    automatic int always_ff_local_var = 1;
    static int always_ff_local_static_var_init = 2;
    int f_res;
    logic [7:0] t_res;
    f_res = simple_func(10);
    simple_task(5, t_res);
    data <= t_res + f_res + module_static_var + module_implicit_static_var_init + always_ff_local_var + always_ff_local_static_var_init;
    o_done <= 1;
  end
endmodule
module ModuleTypes (input wire i_data_in, output logic o_valid_out);
  typedef enum {STATE_IDLE, STATE_BUSY} state_e;
  typedef struct packed {
    logic valid;
    logic [3:0] value;
  } packet_s;
  typedef enum { ERROR_VAL = -1, WARNING_VAL, INFO_VAL, DEBUG_VAL=3, DUMMY_ITEM [1:3] } level_e;
  typedef union packed {
    logic [7:0] byte_field;
    logic [3:0] nibbles_field [1:0];
  } union_s;
  state_e current_state;
  packet_s pkt;
  level_e debug_level_array [0:3];
  struct { bit valid_anon; logic [7:0] data_anon; } anon_struct_var;
  enum { LOW_VAL, HIGH_VAL } anon_enum_var;
  union_s uvar;
  always_comb begin
    current_state = i_data_in ? STATE_BUSY : STATE_IDLE;
    pkt.valid = i_data_in;
    pkt.value = i_data_in ? 4'd5 : 4'd0;
    anon_struct_var.valid_anon = pkt.valid;
    anon_struct_var.data_anon = pkt.value;
    anon_enum_var = i_data_in ? HIGH_VAL : LOW_VAL;
    debug_level_array[0] = ERROR_VAL;
    debug_level_array[1] = WARNING_VAL;
    debug_level_array[2] = INFO_VAL;
    debug_level_array[3] = DEBUG_VAL;
    uvar.byte_field = {anon_struct_var.valid_anon, anon_struct_var.data_anon};
    o_valid_out = pkt.valid;
  end
endmodule
module ModuleParamsConst (input wire i_reset, output logic o_count_done);
  parameter int MAX_COUNT = 10;
  parameter int MIN_VALUE = 0;
  localparam int START_VALUE = '0;
  parameter type MY_TYPE = logic [3:0];
  parameter int NO_DEFAULT;
  parameter logic [7:0] UNBASED_UNSIZED_CONST = 'h5B;
  int counter = START_VALUE;
  MY_TYPE typed_param = 4'hF;
  logic [3:0] derived_value = typed_param;
  logic [7:0] const_derived = UNBASED_UNSIZED_CONST;
  always_ff @(posedge i_reset) begin
    if (i_reset) begin
      counter <= START_VALUE;
    end else begin
      if (counter < MAX_COUNT) begin
        counter <= counter + '1;
      end
    end
    o_count_done <= (counter == MAX_COUNT) || (NO_DEFAULT != 0) || (const_derived == 8'h5B);
  end
endmodule
module ModuleAttrs (input wire i_in_attr, output wire o_out_attr);
  (* keep *) wire internal_signal_keep;
  (* public *) wire public_signal_wire;
  (* public_flat_rw *) logic public_flat_rw_reg;
  (* clock_enable *) logic ignored_attr_reg;
  (* forceable *) logic forceable_reg;
  (* isolate_assignments *) logic isolate_assign_reg;
  (* sformat *) logic sformat_reg;
  (* split_var *) logic split_var_reg;
  (* sc_bv *) logic sc_bv_reg;
  (* clocker *) logic clocker_wire;
  (* no_clocker *) logic no_clocker_wire;
  typedef (* public *) struct { logic pub_f; } public_struct_s;
  public_struct_s pub_struct_var;
  assign internal_signal_keep = i_in_attr;
  assign public_signal_wire = internal_signal_keep;
  assign clocker_wire = i_in_attr;
  assign no_clocker_wire = i_in_attr;
  assign pub_struct_var.pub_f = i_in_attr;
  always @(i_in_attr) begin
    public_flat_rw_reg = ~public_flat_rw_reg;
    ignored_attr_reg = i_in_attr;
    forceable_reg = i_in_attr;
    isolate_assign_reg = i_in_attr;
    sformat_reg = i_in_attr;
    split_var_reg = i_in_attr;
    sc_bv_reg = i_in_attr;
  end
  assign o_out_attr = public_signal_wire | public_flat_rw_reg | forceable_reg | pub_struct_var.pub_f;
endmodule
module ModuleAlwaysPublic (input wire i_in_ap, output wire o_out_ap);
  (* public_flat_rw *) logic pub_reg;
  always @(i_in_ap) begin
    pub_reg = i_in_ap;
  end
  always_public pub_reg;
  assign o_out_ap = pub_reg;
endmodule
module ModuleLoop (input wire i_clk_loop, output logic o_loop_done);
  int count_loop = 0;
  logic done_loop = 0;
  int my_array [0:3];
  static int module_scope_static_var = 100;
  always_ff @(posedge i_clk_loop) begin
    automatic int always_ff_local_var = 5;
    static int always_ff_local_static_var_no_init;
    static int always_ff_local_static_var_init = 1;
    count_loop <= 0;
    done_loop <= 0;
    module_scope_static_var = module_scope_static_var + 1;
    repeat (3) begin
      static int repeat_static_var = 0;
      static int static_in_loop_with_init = 99;
      repeat_static_var = repeat_static_var + static_in_loop_with_init + 1;
      count_loop <= count_loop + 1 + repeat_static_var + always_ff_local_var + always_ff_local_static_var_init;
    end
    done_loop <= 0;
    while (count_loop < 10) begin
      static int while_static_var = 0;
      while_static_var = while_static_var + 1;
      count_loop <= count_loop + 1 + while_static_var;
    end
    count_loop <= 10;
    do begin
      static int do_static_var = 0;
      do_static_var = do_static_var + 1;
      count_loop <= count_loop + 1 + do_static_var;
    end while (count_loop < 15);
    done_loop <= 1;
    foreach (my_array[i]) begin
        static int foreach_static_var = 0;
        foreach_static_var = foreach_static_var + 1;
        my_array[i] = i * 2 + foreach_static_var;
    end
    o_loop_done <= done_loop;
  end
endmodule
module ModuleWait (input wire i_clk_wait, input wire i_enable_wait, output logic o_state_wait_is_2);
  logic [3:0] state_wait;
  always_ff @(posedge i_clk_wait) begin
    state_wait <= 4'b0000;
    wait(i_enable_wait);
    state_wait <= 4'b0001;
    wait(0);
    state_wait <= 4'b0010;
  end
  assign o_state_wait_is_2 = (state_wait == 4'b0010);
endmodule
module SimpleModule (input wire i_in_sm, output wire o_out_sm);
  assign o_out_sm = i_in_sm;
endmodule
module ModuleNamedBegin (input wire i_data_nb, output logic o_flag_nb);
  logic flag_internal_nb;
  always_comb begin : my_comb_block
    if (i_data_nb) begin : then_block
      flag_internal_nb = 1;
    end else begin : else_block
      flag_internal_nb = 0;
    end
  end : my_comb_block
  assign o_flag_nb = flag_internal_nb;
endmodule
module ModuleUnnamedGen (input wire i_en_ug, output logic o_out_ug);
  generate
    if (1) begin
      assign o_out_ug = i_en_ug;
    end
  endgenerate
endmodule
module ModuleGenIf (input wire i_in_genif, output logic o_out_genif);
  generate
    if (1) begin : gen_zero
      assign o_out_genif = i_in_genif;
    end else begin : gen_nonzero
      assign o_out_genif = ~i_in_genif;
    end
  endgenerate
endmodule
module ModuleGenCase #(parameter OPTION = 1) (input wire i_in_gcase, output logic o_out_gcase);
  genvar i;
  generate
    case (OPTION)
      1: begin : opt_one
        assign o_out_gcase = i_in_gcase;
      end
      2: begin : opt_two
        assign o_out_gcase = ~i_in_gcase;
      end
      default: begin : opt_default
        assign o_out_gcase = 1'b0;
      end
    endcase
  endgenerate
endmodule
module ModuleCaseStmt (input wire [1:0] i_select_case, input wire [3:0] i_data_case, output logic [3:0] o_result_case);
  always_comb begin
    case (i_select_case)
      2'b00: o_result_case = i_data_case;
      2'b01: o_result_case = ~i_data_case;
      2'b10: o_result_case = i_data_case + 4'd1;
      default: o_result_case = 4'hZ;
    endcase
  end
endmodule
module ModuleIfElse (input wire i_cond1_if, input wire i_cond2_if, input wire [7:0] i_data_if, output logic [7:0] o_result_if);
  always_comb begin
    if (i_cond1_if) begin
      o_result_if = i_data_if;
    end else if (i_cond2_if) begin
      o_result_if = ~i_data_if;
    end else begin
      o_result_if = 8'b0;
    end
  end
endmodule
module ModuleCheckIndentIf (input wire i_cond_cii, output logic o_out_cii);
  always_comb begin
    logic temp = 0;
    if (i_cond_cii)
      temp = 1;
    o_out_cii = temp;
  end
endmodule
`timescale 1ns / 1ps`
module ModuleTimescale (input wire i_clk_ts, output logic o_valid_ts);
  logic [63:0] current_time;
  logic [63:0] current_realtime;
  int timeunit_int;
  always @(posedge i_clk_ts) begin
    current_time = $time;
    current_realtime = $realtime;
    timeunit_int = $timeunit;
    o_valid_ts <= 1;
  end
endmodule
module ModuleAlwaysCombEventError (input wire i_clk_ace, output logic o_out_ace);
  always_comb begin
    @(posedge i_clk_ace);
    o_out_ace = i_clk_ace;
  end
endmodule
module ModuleEventControl (input wire i_clk_ec, output logic o_out_ec);
  logic state_ec = 0;
  always @(posedge i_clk_ec) begin
    state_ec <= ~state_ec;
  end
  assign o_out_ec = state_ec;
endmodule
module ModuleClocking (input wire i_clk_cb, output wire o_data_out_cb);
  logic data_reg_cb;
  logic [7:0] sampled_data_cb_internal;
  logic bad_output_skew_reg;
  logic output_1step_skew_reg;
  clocking cb @(posedge i_clk_cb);
    default input #1ns output #2ns;
    input i_clk_cb;
    output o_data_out_cb;
    input #5 sampled_data_cb_internal;
    output #1step output_1step_skew_reg;
    output #0 bad_output_skew_reg;
  endclocking
  always_ff @(cb) begin
    data_reg_cb <= 1'b1;
    bad_output_skew_reg <= 1'b1;
    output_1step_skew_reg <= 1'b0;
  end
  always_comb begin
      sampled_data_cb_internal = data_reg_cb ? 8'hAA : 8'h55;
  end
  assign o_data_out_cb = data_reg_cb;
endmodule
module ModuleClassInherit (input wire i_clk_ci, output logic o_done_ci);
  DerivedClass inst_ci;
  always_ff @(posedge i_clk_ci) begin
    if (inst_ci == null) begin
      inst_ci = new();
    end
    if (inst_ci != null) begin
        o_done_ci <= (inst_ci.get_total() == 3);
    end else begin
        o_done_ci <= 0;
    end
  end
endmodule
module ModuleSuperNewErrorInst (input wire i_clk_sne, output logic o_done_sne);
  DerivedClassSuperNewError inst_sne;
  always_ff @(posedge i_clk_sne) begin
    if (inst_sne == null) begin
      inst_sne = new();
    end
    o_done_sne <= (inst_sne != null);
  end
endmodule
module ModulePackageImport (input wire i_en_pi, output logic o_val_pi);
  import my_package::*;
  localparam VAL = PKG_PARAM;
  PkgClass pkg_inst;
  always_comb begin
    if (pkg_inst == null) begin
      pkg_inst = new();
    end
    if (pkg_inst != null) begin
      o_val_pi = i_en_pi ? VAL + pkg_inst.get_pkg_val() : '0;
    end else begin
      o_val_pi = '0;
    end
  end
endmodule
module ModuleClassImportErrorInst (input wire i_en_cie, output logic o_val_cie);
  ClassWithImportError inst_cwi;
  always @(i_en_cie) begin
    if (inst_cwi == null) inst_cwi = new();
    if (inst_cwi != null) begin
      o_val_cie = inst_cwi.get_val();
    end else begin
      o_val_cie = '0;
    end
  end
endmodule
module ModuleConstraintInst (input wire i_data_cn, output logic o_ok_cn);
  ClassWithConstraint req_cn;
  always @(i_data_cn) begin
    if (req_cn == null) req_cn = new();
    if (req_cn != null) begin
        o_ok_cn = req_cn.randomize();
    end else begin
        o_ok_cn = '0;
    end
  end
endmodule
module ModuleCoverInst (input wire i_clk_cov, input wire [1:0] i_state_cov, output logic o_hit_cov);
  covergroup state_cg @(posedge i_clk_cov);
    coverpoint i_state_cov {
      bins state_bins[4] = {0, 1, 2, 3};
    }
  endgroup
  state_cg cg_inst;
  always_ff @(posedge i_clk_cov) begin
    if (cg_inst == null) begin
      cg_inst = new();
    end
    if (cg_inst != null) begin
        cg_inst.sample();
        o_hit_cov <= (cg_inst.get_coverage() > 0);
    end else begin
        o_hit_cov <= 0;
    end
  end
endmodule
module ModuleRestrict (input wire i_a_rp, input wire i_b_rp, output wire o_c_rp);
  property p_example;
    @(posedge i_a_rp) i_b_rp;
  endproperty
  restrict property p_example;
  assign o_c_rp = i_a_rp ^ i_b_rp;
endmodule
module ModuleUnnamedUDP (input wire i_in1_udp, input wire i_in2_udp, output wire o_out_udp);
  wire o_out_anon_udp_named;
  wire o_out_anon_udp_unnamed;
  my_udp anon_udp_inst (o_out_anon_udp_named, i_in1_udp, i_in2_udp);
  my_udp (o_out_anon_udp_unnamed, i_in1_udp, i_in2_udp);
  assign o_out_udp = o_out_anon_udp_named ^ o_out_anon_udp_unnamed;
endmodule
module ModuleNestedGenIf (input wire i_cond_ng, output logic o_out_ng);
  generate
    if (1) begin : outer_gen_named
      assign o_out_ng = 1'b0;
    end else
      if (i_cond_ng) begin : nested_if_begin
        assign o_out_ng = 1'b1;
      end else begin
        assign o_out_ng = 1'b0;
      end
  endgenerate
endmodule
module ModuleInoutDefaultError (input wire i_in_id, output wire o_out_id, inout wire io_data = 1'b1);
  assign o_out_id = i_in_id ^ io_data;
endmodule
module ModuleWireInitializer (input wire i_en_wi, output wire o_out_wi);
  logic initial_var_mod_scope = 1;
  always @(i_en_wi) begin
    int var_init_block = 5;
    o_out_wi = i_en_wi + var_init_block + initial_var_mod_scope;
  end
endmodule
module ModuleGenFor (input wire i_in_gf, output logic o_out_gf);
  genvar i;
  logic dummy_storage [1:0];
  assign o_out_gf = dummy_storage[0] ^ dummy_storage[1];
  generate
    for (i = 0; i < 2; i++) begin : gen_loop
      logic dummy;
      always_comb begin
        dummy = i_in_gf ^ i;
        dummy_storage[i] = dummy;
      end
    end
  endgenerate
endmodule
module ModuleNestedIfBeginGen (input wire i_cond1_nibg, input wire i_cond2_nibg, output logic o_out_nibg);
  generate
    if (i_cond1_nibg)
      assign o_out_nibg = 1'b0;
    else
      if (i_cond2_nibg)
        assign o_out_nibg = 1'b1;
      else
        assign o_out_nibg = 1'b0;
  endgenerate
endmodule
module ModulePkgClassInst (input wire i_clk_pci, output logic o_val_pci);
  import my_package::*;
  PkgClass pkg_inst;
  always @(posedge i_clk_pci) begin
    if (pkg_inst == null) begin
      pkg_inst = new();
    end
    if (pkg_inst != null) begin
      o_val_pci <= pkg_inst.pkg_val;
    end else begin
      o_val_pci <= '0;
    end
  end
endmodule
module ModuleDeepNestedImpliedGen (input wire i_cond1, input wire i_cond2, output logic o_out);
  generate
    if (i_cond1)
      if (i_cond2)
        assign o_out = 1'b1;
      else
        assign o_out = 1'b0;
    else
      if (i_cond2)
        assign o_out = 1'b1;
      else
        assign o_out = 1'b0;
  endgenerate
endmodule
module WrapperModule (input wire i_in_wrap, output wire o_out_wrap);
  wire wrap_sig1;
  wire wrap_sig2;
  SimpleModule sm_inst (
    .i_in_sm(i_in_wrap),
    .o_out_sm(wrap_sig1)
  );
  ModuleClocking mc_inst (
    .i_clk_cb(i_in_wrap),
    .o_data_out_cb(wrap_sig2)
  );
  assign o_out_wrap = wrap_sig1 ^ wrap_sig2;
endmodule
module ModuleIndentIfElse (input wire i_cond1_ie, input wire i_cond2_ie, output logic o_out_ie);
  logic temp = 0;
  always_comb begin
    if (i_cond1_ie)
      temp = 1;
    else if (i_cond2_ie)
      temp = 0;
    else
      temp = 1;
    o_out_ie = temp;
  end
endmodule
module ModuleCheckIndentWhile (input wire i_cond_ciw, input wire [7:0] i_data_ciw, output logic [7:0] o_out_ciw);
  always_comb begin
    logic [7:0] temp = 0;
    int count = 0;
    while(count < 8)
      begin
        temp = temp + (i_data_ciw & (1 << count));
        count = count + 1;
      end
    o_out_ciw = temp;
  end
endmodule
module ModuleCheckIndentRepeat (input wire i_data_cir, output logic [7:0] o_out_cir);
  always_comb begin
    logic [7:0] temp = 0;
    repeat(8)
      begin
        temp = temp + i_data_cir;
      end
    o_out_cir = temp;
  end
endmodule
module ModuleCheckIndentDoWhile (input wire i_data_cidw, output logic [7:0] o_out_cidw);
  logic [7:0] temp = 0;
  int count = 0;
  always_comb begin
    do
      begin
        temp = temp + i_data_cidw;
        count = count + 1;
      end
    while (count < 8);
    o_out_cidw = temp;
  end
endmodule
module ModuleCheckIndentGenIf (input wire i_cond_cig, output logic o_out_cig);
  generate
    if (i_cond_cig)
      begin : then_block
        assign o_out_cig = 1'b1;
      end
    else
      begin : else_block
        assign o_out_cig = 1'b0;
      end
  endgenerate
endmodule
module ModuleCheckIndentGenCase (input wire [1:0] i_sel_cicg, output logic o_out_cicg);
  generate
    case (i_sel_cicg)
      0: begin : case_0
           assign o_out_cicg = 1'b0;
         end
      default: begin : case_def
                 assign o_out_cicg = 1'b1;
               end
    endcase
  endgenerate
endmodule

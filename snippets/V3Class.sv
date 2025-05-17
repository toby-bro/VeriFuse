module ClassBasicInstantiation(
    input int start_val,
    output int final_val
);
  class SimpleAdder;
    int base;
    function new(int initial);
      base = initial;
    endfunction
    function int add_one();
      return base + 1;
    endfunction
  endclass
  SimpleAdder my_adder;
  int computed_final_val_reg;
  assign final_val = computed_final_val_reg;
  initial begin
    my_adder = new(start_val);
    if (my_adder != null) begin
      computed_final_val_reg = my_adder.add_one();
    end else begin
      computed_final_val_reg = 0;
    end
  end
endmodule
module ClassStaticAndParameter(
    input int input_increment,
    output int cumulative_count,
    output int calculated_value
);
  class StaticParamExample;
    static parameter CLASS_MULTIPLIER = 10;
    static int static_counter = 0;
    int instance_value;
    function new(int initial_inst_val);
      instance_value = initial_inst_val;
    endfunction
    static task update_static_counter(input int increment);
      static_counter += increment;
    endtask
    function int get_multiplied_value();
      return instance_value * CLASS_MULTIPLIER;
    endfunction
  endclass
  StaticParamExample instance_one;
  int cumulative_count_reg = 0;
  int calculated_value_reg = 0;
  assign cumulative_count = cumulative_count_reg;
  assign calculated_value = calculated_value_reg;
  initial begin
    instance_one = new(input_increment);
    StaticParamExample::update_static_counter(input_increment);
    cumulative_count_reg = StaticParamExample::static_counter;
    if (instance_one != null) begin
      calculated_value_reg = instance_one.get_multiplied_value();
    end else begin
      calculated_value_reg = 0;
    end
  end
endmodule
module ClassInheritance(
    input bit select_base,
    input int data_in_ih,
    output int output_data_result
);
  class BaseProcessor;
    localparam BASE_OFFSET = 100;
    int initial_offset = BASE_OFFSET;
    function new();
    endfunction
    virtual function int process_data(int data);
      return data + initial_offset;
    endfunction
  endclass
  class DerivedProcessor extends BaseProcessor;
    localparam DERIVED_FACTOR = 5;
    int derived_factor = DERIVED_FACTOR;
    function new();
      super.new();
    endfunction
    function int process_data(int data); 
      return (data + initial_offset) * derived_factor;
    endfunction
  endclass
  BaseProcessor processor_handle;
  BaseProcessor base_inst;
  DerivedProcessor derived_inst;
  int result_val_reg;
  assign output_data_result = result_val_reg;
  initial begin
    base_inst = new();
    derived_inst = new();
    if (select_base) begin
      processor_handle = base_inst;
    end else begin
      processor_handle = derived_inst;
    end
    if (processor_handle != null) begin
      result_val_reg = processor_handle.process_data(data_in_ih);
    end else begin
      result_val_reg = 0;
    end
  end
endmodule
module InterfaceImplementation(
    input byte input_byte,
    input bit select_converter,
    output byte modified_byte_out
);
  interface class ByteConverter;
    pure virtual function byte convert(byte data);
  endclass
  class InvertConverter implements ByteConverter;
    function new();
    endfunction
    function byte convert(byte data);
      return ~data;
    endfunction
  endclass
  class AddOneConverter implements ByteConverter;
    function new();
    endfunction
    function byte convert(byte data);
      return data + 1;
    endfunction
  endclass
  ByteConverter converter_h;
  InvertConverter invert_inst;
  AddOneConverter addone_inst;
  byte converted_val_reg;
  assign modified_byte_out = converted_val_reg;
  initial begin
    invert_inst = new();
    addone_inst = new();
    if (select_converter) begin
      converter_h = invert_inst;
    end else begin
      converter_h = addone_inst;
    end
    if (converter_h != null) begin
      converted_val_reg = converter_h.convert(input_byte);
    end else begin
      converted_val_reg = 0;
    end
  end
endmodule
module ExtendsAndImplementsMultiple(
    input int seed_val,
    input bit select_impl_class,
    output int complex_derived_output
);
  interface class CalculationProvider;
    pure virtual function int provide_calculation();
  endclass
  class SimpleCalculation implements CalculationProvider;
    int simple_base = 500;
    function new();
    endfunction
    virtual function int provide_calculation(); 
      return simple_base;
    endfunction
  endclass
  class ComplexCalculation extends SimpleCalculation implements CalculationProvider;
    int complex_offset = 150;
    function new(int extra);
      super.new();
      complex_offset += extra;
    endfunction
    function int provide_calculation(); 
      return simple_base + complex_offset;
    endfunction
  endclass
  CalculationProvider calc_handle;
  SimpleCalculation simple_inst;
  ComplexCalculation complex_inst;
  int output_val_reg;
  assign complex_derived_output = output_val_reg;
  initial begin
    if (select_impl_class) begin
        complex_inst = new(seed_val);
        calc_handle = complex_inst;
    end else begin
        simple_inst = new();
        calc_handle = simple_inst;
    end
    if (calc_handle != null) begin
      output_val_reg = calc_handle.provide_calculation();
    end else begin
      output_val_reg = 0;
    end
  end
endmodule
module PackedTypesAndTypedefs(
    input bit [31:0] dword_in,
    input shortint short_in,
    output longint result_longint
);
  typedef public struct packed {
    int field_a;
    bit [15:0] field_b;
  } public_struct_t;
  typedef struct packed {
    byte byte_c;
    byte byte_d;
  } private_struct_t;
  typedef public union packed {
    int u_int_field;
    longint u_long_field;
    public_struct_t u_nested_struct;
  } public_union_t;
  typedef public struct packed {
    public_struct_t nested_pub_struct;
    private_struct_t nested_priv_struct;
  } complex_packed_t;
  public_struct_t ps_var;
  private_struct_t priv_s_var;
  public_union_t pu_var;
  complex_packed_t complex_var;
  assign ps_var.field_a = dword_in[31:0];
  assign ps_var.field_b = dword_in[15:0];
  assign priv_s_var.byte_c = short_in[7:0];
  assign priv_s_var.byte_d = short_in[15:8];
  assign pu_var.u_int_field = dword_in[31:0];
  assign pu_var.u_nested_struct = ps_var;
  assign complex_var.nested_pub_struct = ps_var;
  assign complex_var.nested_priv_struct = priv_s_var;
  assign result_longint = pu_var.u_long_field + complex_var.nested_pub_struct.field_a;
endmodule
module ClassAndInitialBlocks(
    input int setup_param_val,
    output int calculation_out
);
  class ClassWithInitial;
    static int static_initial_val = 10;
    int instance_val;
    static initial begin
      static_initial_val += 5;
    end
    function new(int initial);
      instance_val = initial + static_initial_val;
    endfunction
    static task set_static_val(int val);
      static_initial_val = val;
    endtask
    function int calculate();
      return instance_val + static_initial_val;
    endfunction
  endclass
  static int module_static_initial = 5;
  int calculation_out_reg = 0;
  ClassWithInitial class_handle;
  assign calculation_out = calculation_out_reg;
  initial begin
    module_static_initial += 2;
  end
  initial static begin
    ClassWithInitial::set_static_val(setup_param_val + module_static_initial);
  end
  initial begin
    class_handle = new(setup_param_val);
    if (class_handle != null) begin
      calculation_out_reg = class_handle.calculate();
    end else begin
      calculation_out_reg = 0;
    end
  end
endmodule
module ClassCoverageGroup(
    input logic clock_coverage,
    input byte event_value,
    input bit enable_sampling,
    output bit coverage_goal_met
);
  class CoverageExample;
    covergroup EventCoverage @(posedge clock_coverage);
      event_cp : coverpoint event_value {
        bins low = {[0:63]};
        bins mid = {[64:191]};
        bins high = {[192:255]};
        ignore_bins ignored = {127, 128};
      }
    endgroup
    EventCoverage event_cg_inst;
    function new();
      event_cg_inst = new();
    endfunction
    function void do_sample(byte value);
      event_cg_inst.sample(value);
    endfunction
    function int get_coverage_percent();
       return event_cg_inst.get_coverage();
    endfunction
  endclass
  CoverageExample coverage_h;
  bit coverage_goal_met_reg = 0;
  assign coverage_goal_met = coverage_goal_met_reg;
  initial begin
    coverage_h = new();
  end
  always @(posedge clock_coverage) begin
    if (coverage_h != null && enable_sampling) begin
      coverage_h.do_sample(event_value);
      coverage_goal_met_reg = (coverage_h.get_coverage_percent() >= 80);
    end
  end
endmodule
module DPIDeclarationAndUse(
    input int dpi_input_arg,
    input bit enable_dpi_call,
    output int dpi_output_res
);
  import "DPI-C" function int process_with_c(input int value);
  int dpi_output_res_reg = 0;
  assign dpi_output_res = dpi_output_res_reg;
  initial begin
    if (enable_dpi_call) begin
      dpi_output_res_reg = process_with_c(dpi_input_arg);
    end else begin
      dpi_output_res_reg = 0;
    end
  end
endmodule
module ClassHandleTypedef(
    input int initial_val_td,
    output int processed_val_td
);
  class DataProcessor;
    int value;
    function new(int initial);
      value = initial;
    endfunction
    function int get_doubled();
      return value * 2;
    endfunction
  endclass
  typedef DataProcessor DataProcessorHandle_t;
  DataProcessorHandle_t processor_h;
  int result_val_td_reg;
  assign processed_val_td = result_val_td_reg;
  initial begin
    processor_h = new(initial_val_td);
    if (processor_h != null) begin
      result_val_td_reg = processor_h.get_doubled();
    end else begin
      result_val_td_reg = 0;
    end
  end
endmodule
module ClassAccessModifiers(
    input int input_seed_am,
    output int output_derived_calc_am
);
  class BaseWithProtected;
    protected int protected_base_val = 100;
    function new(int seed);
      protected_base_val += seed;
    endfunction
    protected function int get_protected();
      return protected_base_val;
    endfunction
  endclass
  class DerivedWithAccess extends BaseWithProtected;
    local int local_val = 50; 
    private int private_val = 20;
    public int public_val = 5;
    int automatic_val_member = 1; 
    function new(int seed);
      super.new(seed);
      local_val += seed;
      private_val += seed;
      public_val += seed;
      automatic_val_member += seed;
    endfunction
    function int calculate_sum();
      return protected_base_val + local_val + private_val + public_val + automatic_val_member;
    endfunction
    local function int get_local(); return local_val; endfunction
    private function int get_private(); return private_val; endfunction
    public function int get_public(); return public_val; endfunction
  endclass
  DerivedWithAccess instance_h_am;
  int result_val_am_reg;
  assign output_derived_calc_am = result_val_am_reg;
  initial begin
    instance_h_am = new(input_seed_am);
    if (instance_h_am != null) begin
      result_val_am_reg = instance_h_am.calculate_sum();
    end else begin
      result_val_am_reg = 0;
    end
  end
endmodule
module ClassConstMember(
    input int initial_val_const,
    output int output_multiplied_const
);
  class ConstExample;
    const int MULTIPLIER = 7;
    int base_value;
    function new(int initial);
      base_value = initial;
    endfunction
    function int multiply_base();
      return base_value * MULTIPLIER;
    endfunction
  endclass
  ConstExample inst_h_const;
  int result_val_const_reg;
  assign output_multiplied_const = result_val_const_reg;
  initial begin
    inst_h_const = new(initial_val_const);
    if (inst_h_const != null) begin
      result_val_const_reg = inst_h_const.multiply_base();
    end else begin
      result_val_const_reg = 0;
    end
  end
endmodule
module NestedPackedTypes(
    input bit [31:0] data_in_a_np,
    input bit [7:0] data_in_b_np,
    output int output_field_sum_np
);
  typedef public struct packed {
    int field1;
    struct packed { 
      byte sub_field_x;
      byte sub_field_y;
    } sub_struct;
  } outer_struct_t;
  outer_struct_t data_var_np;
  assign data_var_np.field1 = data_in_a_np;
  assign data_var_np.sub_struct.sub_field_x = data_in_b_np;
  assign data_var_np.sub_struct.sub_field_y = ~data_in_b_np;
  assign output_field_sum_np = data_var_np.field1 + data_var_np.sub_struct.sub_field_x + data_var_np.sub_struct.sub_field_y;
endmodule

module class_simple_mod (
    input bit clk_i,
    input int value_i,
    output int value_o
);
  class SimpleClass;
    int member_var;
    function new();
      member_var = 0;
    endfunction
    task set_value(input int val);
      member_var = val;
    endtask
    function int get_value();
      return member_var;
    endfunction
  endclass
  SimpleClass my_instance;
  int local_value;
  always_comb begin
    my_instance = new();
    my_instance.set_value(value_i);
    local_value = my_instance.get_value();
  end
  assign value_o = local_value;
endmodule
module class_static_mod (
    input bit enable_i,
    input int increment_i,
    output int static_value_o
);
  class StaticClass;
    static int s_member_var = 100;
    static task s_increment(input int inc);
      s_member_var += inc;
    endtask
    static function int get_s_member_var();
        return s_member_var;
    endfunction
  endclass
  always_comb begin
    if (enable_i) begin
      StaticClass::s_increment(increment_i);
    end
  end
  assign static_value_o = StaticClass::get_s_member_var();
endmodule
module class_basic_mod (
    input int input_val,
    output int output_val
);
  class BasicClass;
    int data;
    function new(int val);
      data = val;
    endfunction
    function int get_data();
      return data;
    endfunction
  endclass
  BasicClass inst;
  int temp_data;
  always_comb begin
    inst = new(input_val);
    temp_data = inst.get_data();
  end
  assign output_val = temp_data;
endmodule
module typedef_struct_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
  typedef struct packed {
    logic [7:0] field1;
    logic [7:0] field2;
  } my_packed_struct_t;
  my_packed_struct_t my_struct_var;
  always_comb begin
    my_struct_var = packed_in;
  end
  assign field2_o = my_struct_var.field2;
endmodule
module typedef_union_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field0_byte_o
);
  typedef union packed {
    logic [15:0] word;
    logic [1:0][7:0] byte_fields;
  } my_packed_union_t;
  my_packed_union_t my_union_var;
  always_comb begin
    my_union_var.word = packed_in;
  end
  assign field0_byte_o = my_union_var.byte_fields[0];
endmodule
module class_extends_mod (
    input int base_val_i,
    input int derived_val_i,
    output int result_o
);
  class BaseClass;
    int base_member;
    function new(int val);
      base_member = val;
    endfunction
    function int get_base();
      return base_member;
    endfunction
  endclass
  class DerivedClass extends BaseClass;
    int derived_member;
    function new(int b_val, int d_val);
      super.new(b_val);
      derived_member = d_val;
    endfunction
    function int get_derived();
      return derived_member;
    endfunction
    function int sum_members();
      return base_member + derived_member;
    endfunction
  endclass
  DerivedClass derived_instance;
  int calculation_result;
  always_comb begin
    derived_instance = new(base_val_i, derived_val_i);
    calculation_result = derived_instance.sum_members();
  end
  assign result_o = calculation_result;
endmodule
module class_struct_member_mod (
    input logic [15:0] struct_in,
    output logic [7:0] struct_f1_out
);
  typedef struct packed {
    logic [7:0] f1;
    logic [7:0] f2;
  } my_inner_struct_t;
  class ClassWithStruct;
    my_inner_struct_t member_struct;
    function new();
      member_struct.f1 = 8'h00;
      member_struct.f2 = 8'h00;
    endfunction
    task set_fields(input logic [15:0] val);
      member_struct = val;
    endtask
    function logic [7:0] get_f1();
      return member_struct.f1;
    endfunction
  endclass
  ClassWithStruct inst;
  logic [7:0] temp_f1;
  always_comb begin
    inst = new();
    inst.set_fields(struct_in);
    temp_f1 = inst.get_f1();
  end
  assign struct_f1_out = temp_f1;
endmodule
module nested_types_mod (
    input logic [31:0] nested_in,
    output logic [7:0] inner_field_o
);
  typedef struct packed {
    logic [7:0] inner_field;
    logic [7:0] padding;
  } inner_struct_t;
  typedef union packed {
    logic [31:0] full_word;
    struct packed {
      logic [15:0] unused;
      inner_struct_t inner_data;
    } outer_fields;
  } outer_union_t;
  outer_union_t nested_var;
  always_comb begin
    nested_var.full_word = nested_in;
  end
  assign inner_field_o = nested_var.outer_fields.inner_data.inner_field;
endmodule
module class_param_mod (
    input logic [15:0] param_in,
    output logic [15:0] param_out
);
  class ParamClass #(parameter int WIDTH = 8);
    logic [WIDTH-1:0] value;
    function new();
      value = '0;
    endfunction
    task set_value(input logic [WIDTH-1:0] val);
      value = val;
    endtask
    function logic [WIDTH-1:0] get_value();
      return value;
    endfunction
  endclass
  ParamClass #(16) param_instance;
  logic [15:0] param_value;
  always_comb begin
    param_instance = new();
    param_instance.set_value(param_in);
    param_value = param_instance.get_value();
  end
  assign param_out = param_value;
endmodule
module class_initial_mod (
    input int input_seed,
    output int instance_init_val_o
);
  class InitialClass;
    int instance_var;
    function new(int seed_val);
      instance_var = seed_val;
    endfunction
    function int get_instance_var();
      return instance_var;
    endfunction
  endclass
  InitialClass inst_init;
  int local_instance_val;
  always_comb begin
    inst_init = new(input_seed);
    local_instance_val = inst_init.get_instance_var();
  end
  assign instance_init_val_o = local_instance_val;
endmodule
module typedef_struct_public_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
  typedef struct packed {
    logic [7:0] field1;
    logic [7:0] field2;
  } my_public_packed_struct_t;
  my_public_packed_struct_t my_struct_var;
  always_comb begin
    my_struct_var = packed_in;
  end
  assign field2_o = my_struct_var.field2;
endmodule

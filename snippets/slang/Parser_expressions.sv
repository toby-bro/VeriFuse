package common_defs;
  typedef struct packed {
    logic [7:0] a;
    logic       b;
  } my_struct_t;
  class simple_class;
    int data;
    function new(int v = 0);
      data = v;
    endfunction
    function void set_data(int v);
      data = v;
    endfunction
    function int get_data();
      return data;
    endfunction
  endclass
  class base_c;
    int base_val;
    function new(int v = 0);
      base_val = v;
    endfunction
  endclass
  class derived_c extends base_c;
    int drv_val;
    function new(int bv = 0, int dv = 0);
      super.new(bv);
      drv_val = dv;
    endfunction
    function int sum();
      return base_val + drv_val;
    endfunction
  endclass
endpackage
module expr_demo(
  input  logic [7:0] in_a,
  input  logic       in_b,
  output logic [15:0] out_concat,
  output int          out_calc
);
  import common_defs::*;
  always_comb begin
    out_concat = {in_a, 8'(in_b ? 8'hFF : 8'h00)};
    out_calc   = ((in_a inside {[8'd0:8'd127]}) ? int'(in_a) : -int'(in_a)) + 10;
  end
endmodule
module pattern_demo(
  input  logic [3:0]  in_sel,
  input  logic        in_flag,
  output common_defs::my_struct_t out_struct
);
  import common_defs::*;
  always_comb begin
    out_struct = '{a: {in_sel, in_sel}, b: in_flag};
  end
endmodule
module array_class_demo(
  input  int in_val,
  output int out_sum
);
  import common_defs::*;
  derived_c d_h;
  int dyn_arr[];
  always_comb begin
    d_h = new(in_val, in_val + 1);
    dyn_arr = new[3];
    dyn_arr[0] = in_val;
    dyn_arr[1] = in_val + 1;
    dyn_arr[2] = in_val + 2;
    out_sum = d_h.sum() + dyn_arr.sum();
  end
endmodule
module cast_select_demo(
  input  logic [7:0] in_data,
  output logic [1:0] out_bits
);
  logic [7:0] internal;
  always_comb begin
    internal = in_data;
    out_bits = internal[3 -: 2];
  end
endmodule
module super_new_demo(
  input  int in_val,
  output int out_val
);
  import common_defs::*;
  derived_c d_handle;
  always_comb begin
    d_handle = new(in_val, in_val + 5);
    out_val  = d_handle.sum();
  end
endmodule

module assign_basic #(
    parameter int SIZE = 8
)(
    input  logic [SIZE-1:0] in_a, in_b,
    input  int              in_int,
    input  real             in_real,
    input  logic            clk, rst_n,
    output logic [SIZE-1:0] out_assign,
    output logic [SIZE-1:0] out_plus_eq,
    output logic [SIZE-1:0] out_minus_eq,
    output logic [SIZE-1:0] out_mult_eq,
    output logic [SIZE-1:0] out_div_eq,
    output logic [SIZE-1:0] out_mod_eq,
    output logic [SIZE-1:0] out_and_eq,
    output logic [SIZE-1:0] out_or_eq,
    output logic [SIZE-1:0] out_xor_eq,
    output logic [SIZE-1:0] out_shl_eq,
    output logic [SIZE-1:0] out_shr_eq,
    output logic [SIZE-1:0] out_ashr_eq,
    output logic [SIZE-1:0] out_non_blocking,
    output logic [SIZE-1:0] out_conv_int,
    output int              out_conv_real,
    output logic [SIZE-1:0] out_conv_real_explicit
);
    logic [SIZE-1:0] reg_assign;
    logic [SIZE-1:0] reg_plus_eq;
    logic [SIZE-1:0] reg_minus_eq;
    logic [SIZE-1:0] reg_mult_eq;
    logic [SIZE-1:0] reg_div_eq;
    logic [SIZE-1:0] reg_mod_eq;
    logic [SIZE-1:0] reg_and_eq;
    logic [SIZE-1:0] reg_or_eq;
    logic [SIZE-1:0] reg_xor_eq;
    logic [SIZE-1:0] reg_shl_eq;
    logic [SIZE-1:0] reg_shr_eq;
    logic [SIZE-1:0] reg_ashr_eq;
    logic [SIZE-1:0] reg_non_blocking;
    logic [SIZE-1:0] reg_conv_int;
    int              reg_conv_real;
    logic [SIZE-1:0] reg_conv_real_explicit;
    always_comb begin
        reg_assign = in_a;
        reg_plus_eq = in_a;
        reg_plus_eq += in_b;
        reg_minus_eq = in_a;
        reg_minus_eq -= in_b;
        reg_mult_eq = in_a;
        reg_mult_eq *= in_b;
        if (in_b != 0) begin
            reg_div_eq = in_a;
            reg_div_eq /= in_b;
            reg_mod_eq = in_a;
            reg_mod_eq %= in_b;
        end else begin
            reg_div_eq = 'x;
            reg_mod_eq = 'x;
        end
        reg_and_eq = in_a;
        reg_and_eq &= in_b;
        reg_or_eq = in_a;
        reg_or_eq |= in_b;
        reg_xor_eq = in_a;
        reg_xor_eq ^= in_b;
        reg_shl_eq = in_a;
        if (SIZE > 0) reg_shl_eq <<= in_int % SIZE; else reg_shl_eq = '0;
        reg_shr_eq = in_a;
        if (SIZE > 0) reg_shr_eq >>= in_int % SIZE; else reg_shr_eq = '0;
        reg_ashr_eq = $signed(in_a);
        if (SIZE > 0) reg_ashr_eq >>>= in_int % SIZE; else reg_ashr_eq = '0;
        reg_conv_int = in_int;
        reg_conv_real = int'(in_real);
        reg_conv_real_explicit = logic'(in_real);
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_non_blocking <= '0;
        end else begin
            reg_non_blocking <= in_a + in_b;
        end
    end
    assign out_assign = reg_assign;
    assign out_plus_eq = reg_plus_eq;
    assign out_minus_eq = reg_minus_eq;
    assign out_mult_eq = reg_mult_eq;
    assign out_div_eq = reg_div_eq;
    assign out_mod_eq = reg_mod_eq;
    assign out_and_eq = reg_and_eq;
    assign out_or_eq = reg_or_eq;
    assign out_xor_eq = reg_xor_eq;
    assign out_shl_eq = reg_shl_eq;
    assign out_shr_eq = reg_shr_eq;
    assign out_ashr_eq = reg_ashr_eq;
    assign out_non_blocking = reg_non_blocking;
    assign out_conv_int = reg_conv_int;
    assign out_conv_real = reg_conv_real;
    assign out_conv_real_explicit = reg_conv_real_explicit;
endmodule
module assign_timing (
    input  logic in_a,
    input  logic in_b,
    input  logic clk,
    input  logic rst_n,
    output logic out_blocking_timing,
    output logic out_non_blocking_timing
);
    logic reg_blocking;
    logic reg_non_blocking;
    always @(posedge clk) begin
        reg_blocking = @(negedge clk) in_a;
        reg_non_blocking <= @(posedge clk) in_b;
    end
    assign out_blocking_timing = reg_blocking;
    assign out_non_blocking_timing = reg_non_blocking;
endmodule
typedef struct packed {
    logic [3:0] field1;
    logic       field2;
    logic [2:0] field3;
} my_packed_struct_t;
typedef struct {
    int field_int;
    real field_real;
} my_unpacked_struct_t;
module assign_patterns_simple (
    input logic [7:0] in_vec,
    input int         in_int1, in_int2, in_int3,
    input real        in_real1,
    input int         in_dyn_elem,
    input logic [7:0] in_integral_val,
    output my_packed_struct_t out_struct,
    output logic [7:0] out_fixed_array [1:0],
    output my_unpacked_struct_t out_unpacked_struct,
    output int out_dyn_array [],
    output logic [7:0] out_integral_pattern
);
    my_packed_struct_t reg_struct;
    logic [7:0] reg_fixed_array [1:0];
    my_unpacked_struct_t reg_unpacked_struct;
    int reg_dyn_array [];
    logic [7:0] reg_integral_pattern;
    always_comb begin
        reg_struct = '{ in_vec[3:0], in_vec[4], in_vec[7:5] };
        reg_fixed_array = '{ in_vec, ~in_vec };
        reg_unpacked_struct = '{ in_int1, in_real1 };
        reg_dyn_array = '{in_dyn_elem, in_dyn_elem + 1, in_dyn_elem + 2};
        reg_integral_pattern = '{ in_integral_val[0], in_integral_val[1], in_integral_val[2],
            in_integral_val[3], in_integral_val[4], in_integral_val[5],
            in_integral_val[6], in_integral_val[7] };
    end
    assign out_struct = reg_struct;
    assign out_fixed_array = reg_fixed_array;
    assign out_unpacked_struct = reg_unpacked_struct;
    assign out_dyn_array = reg_dyn_array;
    assign out_integral_pattern = reg_integral_pattern;
endmodule
typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
module assign_pattern_lvalue (
    input logic [7:0] in_vec,
    input logic [38:0] in_packed_for_conv,
    output logic [7:0] out_unpacked_struct_repacked,
    output int out_int_conv,
    output logic out_bit_conv,
    output logic [5:0] out_vec_conv
);
    eight_bit_unpacked_struct_t unpacked_s;
    logic [7:0] reg_unpacked_struct_repacked;
    int int_var;
    logic bit_var;
    logic [5:0] vec_var;
    always_comb begin
        unpacked_s.f1 = in_vec[3:0];
        unpacked_s.f2 = in_vec[4];
        unpacked_s.f3 = in_vec[7:5];
        reg_unpacked_struct_repacked = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
        int_var = in_packed_for_conv[31:0];
        bit_var = in_packed_for_conv[32];
        vec_var = in_packed_for_conv[38:33];
        out_unpacked_struct_repacked = reg_unpacked_struct_repacked;
        out_int_conv = int_var;
        out_bit_conv = bit_var;
        out_vec_conv = vec_var;
    end
endmodule
typedef enum { RED, GREEN, BLUE } color_e;
typedef logic [7:0] assoc_value_t;
typedef int assoc_key_t;
typedef assoc_value_t assoc_array_t [assoc_key_t];
typedef int queue_t [];
module assign_patterns_structured (
    input logic [7:0] in_vec_struct,
    input int         in_int_arr_idx0_val,
    input int         in_int_arr_idx1_val,
    input logic [7:0] in_fixed_arr_def,
    input logic [7:0] in_type_match_val,
    input int         in_unpacked_struct_int,
    input real        in_unpacked_struct_real,
    input my_unpacked_struct_t in_unpacked_struct_def,
    input logic [7:0] in_assoc_arr_val1,
    input logic [7:0] in_assoc_arr_val2,
    input logic [7:0] in_assoc_arr_def_val,
    input int         in_dyn_arr_s_idx0_val,
    input int         in_dyn_arr_s_idx1_val,
    input logic [7:0] in_integral_type_match,
    input logic [7:0] in_integral_default,
    input int in_queue_idx0, in_queue_idx1,
    output my_packed_struct_t out_struct_s,
    output logic [7:0] out_fixed_array_s [1:0],
    output int out_dyn_array_s [],
    output assoc_array_t out_assoc_array_s,
    output my_unpacked_struct_t out_unpacked_struct_s,
    output logic [7:0] out_integral_s,
    output queue_t out_queue_s,
    output my_packed_struct_t out_packed_struct_type_cast
);
    my_packed_struct_t reg_struct_s;
    logic [7:0] reg_fixed_array_s [1:0];
    int reg_dyn_array_s [];
    assoc_array_t reg_assoc_array_s;
    my_unpacked_struct_t reg_unpacked_struct_s;
    logic [7:0] reg_integral_s;
    queue_t reg_queue_s;
    my_packed_struct_t reg_packed_struct_type_cast;
    always_comb begin
        reg_struct_s = '{ field1: in_vec_struct[3:0], field2: in_vec_struct[4], field3: in_vec_struct[7:5] };
        reg_struct_s = '{ default: in_vec_struct };
        reg_struct_s = '{ field1: in_vec_struct[3:0], default: ~in_vec_struct };
        reg_struct_s = '{ logic: in_vec_struct[0], default: in_vec_struct };
        reg_fixed_array_s = '{ 0: in_int_arr_idx0_val, 1: in_int_arr_idx1_val };
        reg_fixed_array_s = '{ default: in_fixed_arr_def };
        reg_fixed_array_s = '{ 0: in_int_arr_idx0_val, default: in_fixed_arr_def };
        reg_dyn_array_s = '{ 0: in_dyn_arr_s_idx0_val, 1: in_dyn_arr_s_idx1_val };
        reg_assoc_array_s = '{ 10: in_assoc_arr_val1, 20: in_assoc_arr_val2 };
        reg_assoc_array_s = '{ default: in_assoc_arr_def_val };
        reg_unpacked_struct_s = '{ field_int: in_unpacked_struct_int, field_real: in_unpacked_struct_real };
        reg_unpacked_struct_s = '{ default: in_unpacked_struct_int };
        reg_unpacked_struct_s = '{ real: in_unpacked_struct_real, default: in_unpacked_struct_int };
        reg_integral_s = '{ bit: in_integral_type_match[0], default: in_integral_default };
        reg_queue_s = '{ 0: in_queue_idx0, 1: in_queue_idx1 };
        reg_packed_struct_type_cast = my_packed_struct_t'{ field1: 4'hF, field2: 1'b1, field3: 3'b101 };
    end
    assign out_struct_s = reg_struct_s;
    assign out_fixed_array_s = reg_fixed_array_s;
    assign out_dyn_array_s = reg_dyn_array_s;
    assign out_assoc_array_s = reg_assoc_array_s;
    assign out_unpacked_struct_s = reg_unpacked_struct_s;
    assign out_integral_s = reg_integral_s;
    assign out_queue_s = reg_queue_s;
    assign out_packed_struct_type_cast = reg_packed_struct_type_cast;
endmodule
typedef struct {
    int f1;
    real f2;
    my_packed_struct_t f3;
} nested_unpacked_struct_t;
module assign_patterns_structured_nested (
    input int         in_int_val,
    input real        in_real_val,
    input my_packed_struct_t in_packed_struct_val,
    input int         in_nested_default_int,
    output nested_unpacked_struct_t out_nested_s
);
    nested_unpacked_struct_t reg_nested_s;
    always_comb begin
        reg_nested_s = '{ default: in_nested_default_int };
        reg_nested_s = '{ int: in_int_val, real: in_real_val, default: in_packed_struct_val };
        reg_nested_s = '{ f1: in_int_val, f2: in_real_val, f3: in_packed_struct_val };
        reg_nested_s = '{ default: in_packed_struct_val };
    end
    assign out_nested_s = reg_nested_s;
endmodule
typedef struct packed {
    logic [3:0] f1;
    logic [3:0] f2;
} simple_struct_t;
typedef simple_struct_t simple_struct_array_t [1:0];
typedef int integral_array_t [1:0];
typedef int queue_r_t [];
typedef struct packed {
    logic [1:0] f_a;
    logic [2:0] f_b;
    logic [3:0] f_c;
    logic [1:0] f_d;
    logic [2:0] f_e;
    logic [3:0] f_f;
} struct_for_repl_t;
module assign_patterns_replicated #(
    parameter int REPL_COUNT_INT = 2,
    parameter int REPL_COUNT_FIXED = 2,
    parameter int REPL_COUNT_DYN = 2,
    parameter int REPL_COUNT_QUEUE = 2
)(
    input logic [7:0] in_repl_item_fixed,
    input int         in_repl_item_dyn_q,
    input logic [17:0] in_packed_val_for_struct,
    input logic [7:0] in_integral_item,
    output logic [15:0] out_integral_r,
    output logic [7:0] out_fixed_array_r [1:0],
    output int out_dyn_array_r [],
    output queue_r_t out_queue_r,
    output struct_for_repl_t out_struct_r
);
    logic [15:0] reg_integral_r;
    logic [7:0] reg_fixed_array_r [1:0];
    int reg_dyn_array_r [];
    queue_r_t reg_queue_r;
    struct_for_repl_t reg_struct_r;
    always_comb begin
        // Fix: Provide 16 elements for 16-bit vector
        reg_integral_r = '{
            in_integral_item, in_integral_item, in_integral_item, in_integral_item,
            in_integral_item, in_integral_item, in_integral_item, in_integral_item,
            in_integral_item, in_integral_item, in_integral_item, in_integral_item,
            in_integral_item, in_integral_item, in_integral_item, in_integral_item
        };
        reg_fixed_array_r = '{ REPL_COUNT_FIXED { in_repl_item_fixed } };
        reg_dyn_array_r = '{ REPL_COUNT_DYN { in_repl_item_dyn_q } };
        reg_queue_r = '{ REPL_COUNT_QUEUE { in_repl_item_dyn_q } };
        reg_struct_r = '{ REPL_COUNT_INT { in_packed_val_for_struct[1:0], in_packed_val_for_struct[4:2], in_packed_val_for_struct[8:5] } };
    end
    assign out_integral_r = reg_integral_r;
    assign out_fixed_array_r = reg_fixed_array_r;
    assign out_dyn_array_r = reg_dyn_array_r;
    assign out_queue_r = reg_queue_r;
    assign out_struct_r = reg_struct_r;
endmodule
module assign_patterns_replicated_struct_array #(
    parameter int REPL_COUNT = 2
)(
    input simple_struct_t in_item_s1,
    input simple_struct_t in_item_s2,
    output simple_struct_array_t out_struct_array_fixed,
    output simple_struct_t out_struct_array_dyn []
);
    simple_struct_array_t reg_struct_array_fixed;
    simple_struct_t reg_struct_array_dyn [];
    always_comb begin
        reg_struct_array_fixed = '{ REPL_COUNT { in_item_s1 } };
        reg_struct_array_dyn = '{ REPL_COUNT { in_item_s1, in_item_s2 } };
    end
    assign out_struct_array_fixed = reg_struct_array_fixed;
    assign out_struct_array_dyn = reg_struct_array_dyn;
endmodule
class my_base_class;
    int base_val;
    function new(int val = 10);
        base_val = val;
    endfunction
endclass
class my_derived_class extends my_base_class;
    int derived_val;
    function new(int derived_init = 20);
        super.new();
        derived_val = derived_init;
    endfunction
endclass
class my_base_class_def;
    int val;
    function new(int v = 100);
        val = v;
    endfunction
endclass
class my_derived_class_def extends my_base_class_def;
    function new(int dummy_arg = 0);
        super.new();
    endfunction
endclass
class my_derived_class_super_explicit extends my_base_class;
    int extra_val;
    function new(int arg1, int arg2);
        super.new(arg1);
        extra_val = arg2;
    endfunction
endclass
module new_classes (
    input int in_base_val,
    input int in_derived_val,
    input int in_derived_super_arg1,
    input int in_derived_super_arg2,
    output int out_base_val,
    output int out_derived_val,
    output int out_derived_super_default_base,
    output int out_derived_super_explicit_base,
    output int out_derived_super_explicit_extra
);
    my_base_class base_h;
    my_derived_class derived_h;
    my_derived_class derived_h_with_args;
    my_derived_class_def derived_h_def;
    my_derived_class_super_explicit derived_h_super_explicit;
    always_comb begin
        base_h = new(in_base_val);
        derived_h = new();
        derived_h_with_args = new(in_derived_val);
        derived_h_def = new();
        derived_h_super_explicit = new(in_derived_super_arg1, in_derived_super_arg2);
        if (base_h != null) out_base_val = base_h.base_val; else out_base_val = -1;
        if (derived_h != null) begin
            out_derived_val = derived_h.derived_val;
            out_derived_super_default_base = derived_h.base_val;
        end else begin
            out_derived_val = -1;
            out_derived_super_default_base = -1;
        end
        if (derived_h_super_explicit != null) begin
            out_derived_super_explicit_base = derived_h_super_explicit.base_val;
            out_derived_super_explicit_extra = derived_h_super_explicit.extra_val;
        end else begin
            out_derived_super_explicit_base = -1;
            out_derived_super_explicit_extra = -1;
        end
    end
endmodule
covergroup my_cg_t (int num_bins, string name_str);
    option.per_instance = 1;
    cp_val : coverpoint num_bins {
        bins small_bins = { 0, 1, 2, 3, 4, 5 };
        bins large_bins = { 95, 96, 97, 98, 99, 100 };
    }
endgroup
class cg_factory;
    my_cg_t h;
    int dummy_out;
    function new(int num_bins, string name_str);
        h = new(num_bins, name_str);
        dummy_out = num_bins;
    endfunction
    function int get_bins();
        if (h != null) return h.get_coverage();
        return 0;
    endfunction
    function int get_dummy_out();
        return dummy_out;
    endfunction
endclass
module new_covergroups_in_class (
    input int in_cg_bins,
    input string in_cg_name,
    output int out_cg_dummy_val
);
    cg_factory factory_h;
    always_comb begin
        factory_h = new(in_cg_bins, in_cg_name);
        if (factory_h != null) out_cg_dummy_val = factory_h.get_dummy_out();
        else out_cg_dummy_val = -1;
    end
endmodule
module child_scalar_port (
    input logic data_in,
    output logic data_out
);
    assign data_out = data_in;
endmodule
module parent_array_conn_scalar (
    input logic [7:0] in_packed_expr,
    output logic out_scalar_ports [7:0]
);
    logic scalar_outs [7:0];
    child_scalar_port children_inst [7:0] (
        .data_in(in_packed_expr),
        .data_out(scalar_outs)
    );
    assign out_scalar_ports = scalar_outs;
endmodule
module child_packed_scalar_port (
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    assign data_out = data_in;
endmodule
module try_connect_port_array_packed_unpacked #(parameter int NUM_INST = 2)(
    input logic [NUM_INST*4-1:0] in_packed_src,
    output logic [3:0] out_packed_ports [NUM_INST-1:0]
);
    logic [3:0] child_out_ports [NUM_INST-1:0];
    child_packed_scalar_port children_inst [NUM_INST-1:0] (
        .data_in(in_packed_src),
        .data_out(child_out_ports)
    );
    assign out_packed_ports = child_out_ports;
endmodule
module child_unpacked_array_port (
    input logic data_in [3:0],
    output logic data_out [3:0]
);
    assign data_out = data_in;
endmodule
module try_connect_port_array_unpacked_unpacked #(parameter int NUM_INST = 2)(
    input logic in_unpacked_src [NUM_INST-1:0][3:0],
    output logic out_unpacked_ports [NUM_INST-1:0][3:0]
);
    logic unpacked_outs [NUM_INST-1:0][3:0];
    child_unpacked_array_port children_inst [NUM_INST-1:0] (
        .data_in(in_unpacked_src),
        .data_out(unpacked_outs)
    );
    assign out_unpacked_ports = unpacked_outs;
endmodule
module try_connect_port_array_multidim #(parameter int D1=2, parameter int D2=4)(
    input logic [D1*D2-1:0] in_packed_expr,
    output logic out_scalar_ports [D1-1:0][D2-1:0]
);
    logic scalar_outs [D1-1:0][D2-1:0];
    child_scalar_port children_inst [D1-1:0][D2-1:0] (
        .data_in(in_packed_expr),
        .data_out(scalar_outs)
    );
    assign out_scalar_ports = scalar_outs;
endmodule
module child_with_defaults (
    input int in_int_default = 5,
    input logic in_logic_default = 1'b1,
    output int out_int,
    output logic out_logic
);
    assign out_int = in_int_default;
    assign out_logic = in_logic_default;
endmodule
module connect_empty_arg (
    input logic dummy_in,
    output int out_int_default,
    output logic out_logic_default,
    output int out_child_int,
    output logic out_child_logic,
    output logic out_dummy_out
);
    child_with_defaults child_defaults_inst (
        .in_int_default(),
        .in_logic_default(),
        .out_int(out_int_default),
        .out_logic(out_logic_default)
    );
    child_with_defaults child_explicit_inst (
        .in_int_default(10),
        .in_logic_default(1'b0),
        .out_int(out_child_int),
        .out_logic(out_child_logic)
    );
    module child_output(output logic out_sig); assign out_sig = 1'b1; endmodule
    child_output child_out_inst (.out_sig());
    assign out_dummy_out = 1'b0;
endmodule
typedef int my_assoc_key_t;
typedef logic [7:0] my_assoc_value_t;
typedef my_assoc_value_t my_assoc_array_t [my_assoc_key_t];
typedef int my_queue_t [];
typedef struct packed { logic [3:0] f1; logic [3:0] f2; } simple_struct_for_lp_t;
typedef struct { int f1; real f2; } unpacked_struct_for_lp_t;
module constant_eval_patterns (
    input logic dummy_in,
    input logic [7:0] in_packed_for_apply_conv_slice,
    output logic [7:0] out_simple_packed,
    output simple_struct_for_lp_t out_simple_packed_struct,
    output int out_simple_fixed_array [1:0],
    output unpacked_struct_for_lp_t out_simple_unpacked_struct,
    output logic [7:0] out_simple_integral,
    output logic [15:0] out_simple_packed_conv,
    output simple_struct_for_lp_t out_structured_packed_struct,
    output logic [7:0] out_structured_fixed_array [1:0],
    output assoc_array_t out_structured_assoc_array,
    output unpacked_struct_for_lp_t out_structured_unpacked_struct,
    output logic [7:0] out_structured_integral,
    output queue_t out_structured_queue,
    output simple_struct_for_lp_t out_replicated_packed_struct,
    output logic [7:0] out_replicated_fixed_array [1:0],
    output logic [15:0] out_replicated_integral,
    output queue_t out_replicated_queue,
    output int out_new_array_eval [],
    output logic [7:0] out_new_array_eval_bits [],
    output logic [7:0] out_new_array_eval_init_single [],
    output logic [7:0] out_new_array_eval_init_multi [],
    output logic [31:0] out_packed_to_int_conv
);
    localparam logic [7:0] LP_SIMPLE_PACKED = '{1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0};
    localparam simple_struct_for_lp_t LP_SIMPLE_PACKED_STRUCT = '{4'hA, 4'h5};
    localparam int LP_SIMPLE_FIXED_ARRAY [1:0] = '{10, 20};
    localparam unpacked_struct_for_lp_t LP_SIMPLE_UNPACKED_STRUCT = '{10, 3.14};
    localparam logic [7:0] LP_SIMPLE_INTEGRAL = '{1,1,0,0,1,1,0,0};
    localparam logic [15:0] LP_SIMPLE_PACKED_FOR_CONV = '{ 16 { 1'b1 } };
    localparam logic [38:0] LP_PACKED_FOR_APPLY_CONV = '{39{1'b1}};
    localparam simple_struct_for_lp_t LP_STRUCTURED_PACKED_STRUCT = '{f1: 4'h1, f2: 4'h2};
    localparam logic [7:0] LP_STRUCTURED_FIXED_ARRAY [1:0] = '{ 0: 8'hAA, 1: 8'h55 };
    localparam my_assoc_array_t LP_STRUCTURED_ASSOC_ARRAY = '{ 10: 8'hAA, 20: 8'h55, default: 8'hFF };
    localparam unpacked_struct_for_lp_t LP_STRUCTURED_UNPACKED_STRUCT = '{f1: 30, f2: 6.28};
    localparam logic [7:0] LP_STRUCTURED_INTEGRAL = '{bit: 1'b1, default: 8'hCC};
    localparam queue_t LP_STRUCTURED_QUEUE = '{ 0: 5, 1: 6 };
    localparam simple_struct_for_lp_t LP_REPLICATED_PACKED_STRUCT = '{ 2 { 4'hA } };
    localparam logic [7:0] LP_REPLICATED_FIXED_ARRAY [1:0] = '{ 2 { 8'hBB } };
    // Fix replicated assignment pattern in localparam: use constant value
    localparam logic [15:0] LP_REPLICATED_INTEGRAL = '{16{8'hAA}};
    // Define LP_REPLICATED_QUEUE as a constant queue
    localparam queue_t LP_REPLICATED_QUEUE = '{1, 2, 3};
    localparam int LP_NEW_ARRAY_EVAL [] = new[5];
    localparam logic [7:0] LP_NEW_ARRAY_EVAL_BITS [] = new[3];
    localparam logic [7:0] LP_NEW_ARRAY_EVAL_INIT_SINGLE [3] = '{8'hAA, 8'hAA, 8'hAA};
    localparam logic [7:0] LP_NEW_ARRAY_EVAL_INIT_MULTI [] = new[4] ('{8'h11, 8'h22});
    localparam logic [31:0] LP_PACKED_TO_INT_CONV = '{ 32 { 1'b1 } };
    always_comb begin
        assign out_simple_packed = LP_SIMPLE_PACKED;
        assign out_simple_packed_struct = LP_SIMPLE_PACKED_STRUCT;
        assign out_simple_fixed_array = LP_SIMPLE_FIXED_ARRAY;
        assign out_simple_unpacked_struct = LP_SIMPLE_UNPACKED_STRUCT;
        assign out_simple_integral = LP_SIMPLE_INTEGRAL;
        assign out_simple_packed_conv = LP_SIMPLE_PACKED_FOR_CONV;
        assign out_structured_packed_struct = LP_STRUCTURED_PACKED_STRUCT;
        assign out_structured_fixed_array = LP_STRUCTURED_FIXED_ARRAY;
        assign out_structured_assoc_array = LP_STRUCTURED_ASSOC_ARRAY;
        assign out_structured_unpacked_struct = LP_STRUCTURED_UNPACKED_STRUCT;
        assign out_structured_integral = LP_STRUCTURED_INTEGRAL;
        assign out_structured_queue = LP_STRUCTURED_QUEUE;
        assign out_replicated_packed_struct = LP_REPLICATED_PACKED_STRUCT;
        assign out_replicated_fixed_array = LP_REPLICATED_FIXED_ARRAY;
        assign out_replicated_integral = LP_REPLICATED_INTEGRAL;
        assign out_replicated_queue = LP_REPLICATED_QUEUE;
        assign out_new_array_eval = LP_NEW_ARRAY_EVAL;
        assign out_new_array_eval_bits = LP_NEW_ARRAY_EVAL_BITS;
        assign out_new_array_eval_init_single = LP_NEW_ARRAY_EVAL_INIT_SINGLE;
        assign out_new_array_eval_init_multi = LP_NEW_ARRAY_EVAL_INIT_MULTI;
        assign out_packed_to_int_conv = LP_PACKED_TO_INT_CONV;
    end
endmodule

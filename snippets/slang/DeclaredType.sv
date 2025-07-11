module ModuleBasicVar (
    input logic [7:0] in1,
    input int in2,
    output logic [7:0] out1,
    output int out2,
    output real out3,
    output logic [3:0][15:0] out4,
    output int out5
);
    logic [7:0] var1 = in1 + 1;
    int var2;
    real var3 = 3.14;
    logic [3:0][15:0] var4 = '0;
    int var5 = '1;
    assign var2 = in2 * 2;
    assign out1 = var1;
    assign out2 = var2;
    assign out3 = var3;
    assign out4 = var4;
    assign out5 = var5;
endmodule
typedef int my_int_t;
module ModuleTypedef (
    input logic [15:0] in_data,
    output my_int_t out_data
);
    my_int_t internal_var = in_data;
    assign out_data = internal_var;
endmodule
module ModuleNets (
    input logic in_logic,
    input tri0 in_tri,
    output wire out_wire,
    output wand out_wand,
    output wire [0:0] out_single_bit
);
    wire net1 = in_logic;
    tri0 net2 = in_tri;
    wand net3;
    wire [0:0] single_bit_wire;
    assign out_wire = net1 | net2;
    assign net3 = 'bz;
    assign out_wand = net3;
    assign single_bit_wire = in_logic;
    assign out_single_bit = single_bit_wire;
endmodule
typedef logic my_net_t;
nettype my_net_t user_net1;
module ModuleUserNet (
    input logic in_logic,
    output my_net_t out_user_net
);
    user_net1 user_net_var = in_logic;
    assign out_user_net = user_net_var;
endmodule
module ModuleParameters #(
    parameter P_VAL = 8,
    parameter type P_TYPE = logic,
    parameter int P_VAR = '1
) (
    input logic [P_VAL-1:0] in_param_val,
    input P_TYPE in_param_type,
    output logic [P_VAL-1:0] out_param_val,
    output int out_param_var,
    output P_TYPE out_param_type
);
    P_TYPE internal_type_var = in_param_type;
    logic [P_VAL-1:0] internal_val_var = in_param_val;
    int internal_var_var = P_VAR;
    specparam SP_DELAY = 5;
    assign out_param_type = internal_type_var;
    assign out_param_val = internal_val_var;
    assign out_param_var = internal_var_var;
endmodule
module ModuleImplicitPort (
    input signed [7:0] data,
    output logic out_valid
);
    logic valid;
    assign valid = |data;
    assign out_valid = valid;
endmodule
module ModuleClassRand (
    input logic clk,
    output int rand_val,
    output bit [3:0] randc_val,
    output logic rand_struct_a
);
    class MyRandClass;
        rand int rand_int;
        randc bit [3:0] randc_bit_vec;
        rand struct { logic a; int b; } rand_struct;
        function new();
        endfunction
    endclass
    MyRandClass my_object;
    int internal_rand_int;
    bit [3:0] internal_randc_vec;
    logic internal_rand_struct_a;
    always_comb begin
        if (my_object == null) begin
            my_object = new();
        end
        if (my_object != null) begin
            internal_rand_int = my_object.rand_int;
            internal_randc_vec = my_object.randc_bit_vec;
            internal_rand_struct_a = my_object.rand_struct.a;
        end else begin
            internal_rand_int = 0;
            internal_randc_vec = '0;
            internal_rand_struct_a = 0;
        end
    end
    assign rand_val = internal_rand_int;
    assign randc_val = internal_randc_vec;
    assign rand_struct_a = internal_rand_struct_a;
endmodule
module ModuleDPI (
    input int in_dpi_arg,
    input logic call_func,
    output real out_dpi_ret,
    output int out_pure_called
);
    import "DPI-C" function real my_dpi_func(int arg1);
    import "DPI-C" function int my_pure_dpi_func();
    real internal_ret;
    int pure_ret_val = 0;
    always_comb begin
        internal_ret = my_dpi_func(in_dpi_arg);
        if (call_func) begin
            pure_ret_val = my_pure_dpi_func();
        end else begin
            pure_ret_val = 0;
        end
    end
    assign out_dpi_ret = internal_ret;
    assign out_pure_called = pure_ret_val;
endmodule
module ModuleCoverage (
    input logic [7:0] coverage_data,
    output logic [7:0] out_cov
);
    property p_nonzero;
        @(posedge coverage_data[0]) $countones(coverage_data) > 0;
    endproperty
    assign out_cov = coverage_data;
endmodule
interface InterfaceForIfaceVar;
    logic clk;
    logic rst;
    logic iface_var1;
    int iface_var2;
    struct { logic a; int b; } iface_struct_var;
endinterface
typedef struct {
    logic field_a;
    int field_b;
} struct_t;
typedef union {
    logic [7:0] field_u1;
    int field_u2;
} union_t;
module ModuleStructUnion (
    input logic [1:0][7:0] in_packed,
    input logic in_a,
    output struct_t out_struct,
    output union_t out_union
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } packed_struct_t;
    packed_struct_t packed_var;
    struct_t struct_var;
    union_t union_var;
    always_comb begin
        packed_var = in_packed;
        struct_var.field_a = in_a;
        struct_var.field_b = packed_var.field1;
        union_var.field_u1 = packed_var.field2;
    end
    assign out_struct = struct_var;
    assign out_union = union_var;
endmodule
typedef enum {
    RED = 0,
    GREEN = 1,
    BLUE = 2
} color_e;
module ModuleEnumInitializer (
    input int in_val,
    output color_e out_color
);
    color_e current_color;
    always_comb begin
        current_color = color_e'(in_val % 3);
    end
    assign out_color = current_color;
endmodule
module ModuleProceduralContext (
    input int in_proc,
    output int out_proc,
    output int out_task_var,
    output logic [7:0] out_func_var
);
    int task_var_output;
    logic [7:0] func_var_output;
    task my_task(input int arg1);
        automatic int task_var = arg1 * 2;
        task_var_output = task_var;
    endtask
    function int my_function(input [7:0] implicit_arg);
        automatic logic [7:0] func_var = implicit_arg + 1;
        func_var_output = func_var;
        return func_var;
    endfunction
    int func_result;
    always_comb begin
        func_result = my_function(in_proc);
        my_task(in_proc + 10);
    end
    assign out_proc = func_result;
    assign out_task_var = task_var_output;
    assign out_func_var = func_var_output;
endmodule
module ModuleInterconnectNet (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    interconnect [7:0] my_interconnect;
    logic [7:0] internal_data;
    assign internal_data = in_data;
    assign out_data = internal_data;
endmodule

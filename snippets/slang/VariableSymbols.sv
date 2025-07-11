package package_with_nets;
    wire [7:0] package_net_init;
    wire [7:0] package_net_no_init;
endpackage
nettype logic logic_buf;
class my_class;
    int data;
    function new(int initial_data);
        data = initial_data;
    endfunction
endclass
module VariableLifetimes (
    input  logic        clk,
    output logic [7:0]  out_static,
    output logic [7:0]  out_automatic_proc,
    output logic [7:0]  out_automatic_func,
    output logic        out_const
);
    logic [7:0] module_static_var = 8'hAA;
    static logic [7:0] explicit_static_var = 8'h55;
    const  logic const_module_var = 1'b1;
    logic [7:0] func_result_reg;
    always @(posedge clk) begin
        logic [7:0] block_automatic_var;
        automatic logic [7:0] explicit_automatic_var;
        static    logic [7:0] static_in_proc_init = 8'h11;
        block_automatic_var      = module_static_var + 1;
        explicit_automatic_var   = explicit_static_var + 1;
        out_static               <= module_static_var + explicit_static_var + static_in_proc_init;
        out_automatic_proc       <= block_automatic_var + explicit_automatic_var;
        out_const                <= const_module_var;
        func_result_reg          <= call_func_wrapper(block_automatic_var);
    end
    assign out_automatic_func = func_result_reg;
    function automatic void call_func(input logic [7:0] in_arg);
        automatic logic [7:0] func_automatic_var;
        static    logic [7:0] func_static_var = 8'h33;
        func_automatic_var = in_arg + 1 + func_static_var;
    endfunction
    function automatic logic [7:0] call_func_wrapper(input logic [7:0] in_arg);
        automatic logic [7:0] func_automatic_var;
        static    logic [7:0] func_static_var_w = 8'h44;
        func_automatic_var = in_arg + 1 + func_static_var_w;
        call_func(func_automatic_var);
        return func_automatic_var;
    endfunction
endmodule
module ForLoopVars (
    input  logic [3:0] limit,
    output logic [7:0] sum
);
    logic [7:0] temp_sum;
    always_comb begin
        temp_sum = 8'b0;
        for (logic [3:0] i = 0; i < limit; i++) begin
            temp_sum = temp_sum + i;
        end
        for (int i_int = 0, j_var = i_int; i_int < limit; i_int++) begin
            temp_sum = temp_sum + j_var;
        end
        sum = temp_sum;
    end
endmodule
module StaticInitializerCheck (
    input  logic [7:0] in_var,
    input  wire  [7:0] in_net,
    output logic [7:0] out_val
);
    static logic [7:0] static_var_a                 = 8'h10;
    static logic [7:0] static_var_b                 = static_var_a + 1;
    static logic [7:0] static_var_c                 = 8'h20;
    static logic [7:0] static_var_d                 = static_var_c + 1;
    static logic [7:0] static_var_ref_input_diag    = in_var + 1;
    static logic [7:0] static_var_ref_net_diag      = in_net + 1;
    static logic [7:0] static_var_ref_func          = get_static_val() + 1;
    static logic [7:0] static_var_ref_sys           = $bits(in_var) + 1;
    static logic [7:0] static_var_e                 = 8'h30;
    static logic [7:0] static_var_ref_after_diag    = static_var_e + 1;
    always_comb begin
        out_val = static_var_b               +
                  static_var_d               +
                  static_var_ref_func        +
                  static_var_ref_sys         +
                  static_var_ref_input_diag  +
                  static_var_ref_net_diag    +
                  static_var_ref_after_diag  +
                  static_var_e;
    end
    function automatic logic [7:0] get_static_val();
        return static_var_a * 2;
    endfunction
endmodule
module FormalArguments (
    input  logic [7:0] in_val,
    inout  wire  [7:0] inout_port,
    output logic [7:0] out_val,
    output logic [7:0] out_task_val
);
    logic [7:0] func_sum_out_reg;
    logic [7:0] inout_port_driver_reg;
    logic [7:0] task_out_reg;
    logic [7:0] task_inout_driver_reg;
    assign inout_port = inout_port_driver_reg;
    always_comb begin
        static logic [7:0] temp_inout_func       = inout_port_driver_reg;
        logic  [7:0]       temp_sum_out;
        static logic [7:0] const_ref_input_val   = in_val + 2;
        static logic [7:0] temp_task_inout       = inout_port_driver_reg;
        logic  [7:0]       temp_task_out;
        temp_sum_out = add_values(in_val, 8'h10, temp_sum_out,
                                  temp_inout_func, const_ref_input_val);
        inout_port_driver_reg = temp_inout_func;
        func_sum_out_reg      = temp_sum_out;
        call_task(in_val, temp_task_inout, temp_task_out);
        inout_port_driver_reg = temp_task_inout;
        task_out_reg          = temp_task_out;
        out_val       = func_sum_out_reg;
        out_task_val  = task_out_reg;
    end
    function automatic logic [7:0] add_values(
        input  logic [7:0] a,
        input  logic [7:0] b = 8'h05,
        output logic [7:0] sum_out,
        ref    logic [7:0] inout_arg,
        const  ref logic [7:0] const_ref_arg
    );
        sum_out   = a + b;
        inout_arg = inout_arg + a + const_ref_arg;
        return sum_out;
    endfunction
    task automatic call_task(
        input  logic [7:0] task_in,
        inout  logic [7:0] task_inout,
        output logic [7:0] task_out
    );
        task_out  = task_in + 8'h01;
        task_inout = task_inout + 8'h02;
    endtask
endmodule
module FunctionImplicitTypes (
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] implicit_result_var;
    always_comb begin
        data_out = add_implicit(data_in, 8'h03, implicit_result_var);
    end
    function logic [7:0] add_implicit(
        input  logic [7:0] data_a,
        input  logic [7:0] data_b,
        output logic [7:0] result
    );
        result = data_a + data_b;
        return result;
    endfunction
endmodule
module NetDeclarations (
    input  logic clk,
    input  logic reset,
    output wire  out_wire,
    output wire  out_delay,
    output wire  out_strength_drive,
    output wire  out_strength_charge,
    output wire  out_tri,
    output wire [7:0] out_vec,
    output wire  out_scalared_compat,
    output wire  out_trireg
);
    wire basic_wire; assign basic_wire = clk; assign out_wire = basic_wire;
    logic basic_logic; always_comb basic_logic = reset;
    tri basic_tri; assign basic_tri = clk & reset; assign out_tri = basic_tri;
    wand basic_wand; assign basic_wand = 1'b1; assign basic_wand = 1'b0;
    wor basic_wor;  assign basic_wor  = 1'b1; assign basic_wor  = 1'b0;
    triand basic_triand; assign basic_triand = 1'b1; assign basic_triand = 1'b0;
    trior  basic_trior;  assign basic_trior  = 1'b1; assign basic_trior  = 1'b0;
    tri0 basic_tri0; assign basic_tri0 = clk ? 1'b1 : 1'bz;
    tri1 basic_tri1; assign basic_tri1 = reset ? 1'b0 : 1'bz;
    supply0 basic_supply0;
    supply1 basic_supply1;
    trireg basic_trireg; assign basic_trireg = basic_tri; assign out_trireg = basic_trireg;
    wire [7:0] vector_wire;
    assign vector_wire = {clk, clk, clk, clk, clk, clk, clk, reset};
    assign out_vec = vector_wire;
    wire single_scalared_compat; assign single_scalared_compat = clk; assign out_scalared_compat = single_scalared_compat;
    wire vectored [3:0] single_vectored; assign single_vectored = {4{reset}};
    wire scalared [7:0] vector_scalared; assign vector_scalared = vector_wire;
    wire vectored [7:0] vector_vectored; assign vector_vectored = vector_wire;
    wire delay_wire_scalar; assign delay_wire_scalar = clk; assign out_delay = delay_wire_scalar;
    wire [15:0] delay_wire_vector; assign delay_wire_vector = {16{reset}};
    wire (strong1, strong0) drive_strength_wire = 1'bz;
    assign drive_strength_wire = clk; assign out_strength_drive = drive_strength_wire;
    trireg (large)  charge_strength_large;  assign charge_strength_large  = basic_tri; assign out_strength_charge = charge_strength_large;
    trireg (medium) charge_strength_medium; assign charge_strength_medium = basic_tri;
    trireg (small)  charge_strength_small;  assign charge_strength_small  = basic_tri;
endmodule
module ImplicitNet (
    input  logic in_val,
    output wire  out_val
);
    assign implicit_wire = in_val;
    assign out_val = implicit_wire;
endmodule
module PackageNetCheck (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    import package_with_nets::*;
    assign package_net_no_init = in_val;
    assign package_net_init    = in_val + 1;
    always_comb begin
        out_val = package_net_init + package_net_no_init;
    end
endmodule
module ForeachLoop (
    input  logic [3:0] in_array [0:7],
    output logic [7:0] out_sum
);
    logic [7:0] temp_sum;
    always_comb begin
        temp_sum = 8'b0;
        foreach (in_array[i]) begin
            temp_sum = temp_sum + in_array[i];
        end
        out_sum = temp_sum;
    end
endmodule
module AssignmentPatterns (
    input  logic [15:0] in_val,
    output logic [7:0]  out_struct_a,
    output logic [7:0]  out_struct_b,
    output logic [23:0] out_repl,
    output logic        out_pattern_var
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } my_struct_t;
    my_struct_t struct_var;
    logic [7:0] repl_array [0:2];
    logic pattern_case_temp;
    always_comb begin
        struct_var     = '{ field_a: in_val[7:0], field_b: in_val[15:8] };
        out_struct_a   = struct_var.field_a;
        out_struct_b   = struct_var.field_b;
        repl_array     = '{ 3 { in_val[7:0] } };
        out_repl       = {repl_array[0], repl_array[1], repl_array[2]};
        case (in_val)
            16'h0000: pattern_case_temp = 1'b0;
            16'h0001: begin
                logic [15:0] pat_var_item = in_val;
                pattern_case_temp = |pat_var_item;
            end
            default: pattern_case_temp = |in_val;
        endcase
        out_pattern_var = pattern_case_temp;
    end
endmodule
module ClassVariableInstantiation (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    my_class my_object;
    int      object_data;
    always_comb begin
        if (in_val != 0) begin
            my_object   = new(in_val);
            object_data = my_object.data;
        end
        else begin
            object_data = 0;
        end
        out_val = object_data;
    end
endmodule
module UserDefinedNettype (
    input  logic in_val,
    output wire  out_val
);
    logic_buf my_custom_net;
    assign my_custom_net = in_val;
    assign out_val       = my_custom_net;
endmodule
module StructExample (
    input  logic [15:0] in_data,
    output logic [7:0]  out_field_a,
    output logic [7:0]  out_field_b
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } example_struct_t;
    example_struct_t my_struct;
    always_comb begin
        my_struct     = in_data;
        out_field_a   = my_struct.field_a;
        out_field_b   = my_struct.field_b;
    end
endmodule

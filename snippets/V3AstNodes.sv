timeunit 1ns;
timeprecision 1ps;
module mod_basic (
    input logic in_basic_a,
    output logic out_basic_b
);
    wire w_basic_c;
    logic r_basic_d;
    assign w_basic_c = in_basic_a;
    always_comb begin
        r_basic_d = w_basic_c;
    end
    assign out_basic_b = r_basic_d;
endmodule
module mod_data_types #(parameter int WIDTH = 8) (
    input byte in_scalar,
    input logic [WIDTH-1:0] in_packed_vec,
    input int in_unpacked_arr [0:3],
    input logic [7:0] in_pat_match,
    output real out_real,
    output shortint out_packed_arr [3:0],
    output int out_unpacked_arr_scalar,
    output logic [7:0] out_pat_match,
    output logic [15:0] out_streaming_concat,
    output int out_clog2,
    output logic public_output
);
    longint local_longint;
    bit [1:0][7:0] local_2d_packed;
    byte local_2d_unpacked [0:1][0:7];
    logic local_sc_var;
    tri local_tri_wire;
    assign local_tri_wire = 1'bz;
    typedef int my_int_t;
    my_int_t local_typedef_int;
    always_comb begin @*
        local_longint = $signed(in_packed_vec);
        out_real = $real(in_scalar);
        for (int i = 0; i < 4; i++) begin
            logic [1:0] temp_slice;
            temp_slice = in_packed_vec[i*2 +: 2];
            out_packed_arr[i] = {{14{1'b0}}, temp_slice};
        end
        local_typedef_int = in_unpacked_arr[0];
        out_unpacked_arr_scalar = local_typedef_int;
        for (int i = 0; i < 2; i++) begin
            for (int j = 0; j < 8; j++) begin
                local_2d_unpacked[i][j] = in_scalar + i + j;
            end
        end
        local_2d_packed[0] = in_packed_vec;
        local_2d_packed[1] = in_packed_vec + 1;
        out_pat_match = in_pat_match;
        out_streaming_concat = {>>{in_packed_vec, in_scalar}};
        out_clog2 = $clog2(WIDTH);
        local_sc_var = out_clog2[0];
        public_output = local_sc_var;
    end
endmodule
module mod_struct_enum_typedef (
    input logic [1:0] in_enum_val_sel,
    input logic [7:0] in_struct_val_mem1,
    input int in_struct_val_arr,
    output int out_enum_int,
    output byte out_struct_member,
    output int out_struct_arr_member,
    output bit out_void_func_dummy
);
    typedef enum {RED, GREEN, BLUE} color_e;
    color_e local_enum_var;
    typedef struct packed {
        byte member1;
        shortint member2;
        int member_arr [0:2];
    } my_struct_t;
    typedef struct packed {
        my_struct_t nested_struct;
        int nested_member;
    } my_nested_struct_t;
    my_nested_struct_t local_nested_struct_var;
    typedef union packed {
        int u_int;
        logic [31:0] u_vec;
    } my_union_t;
    my_union_t local_union_var;
    typedef struct {
        int u_member1;
        byte u_member2;
    } my_unpacked_struct_t;
    my_unpacked_struct_t local_unpacked_struct_var;
    function void my_void_function(input bit dummy, output bit out_dummy);
        out_dummy = dummy;
    endfunction: my_void_function
    always_comb begin @*
        case (in_enum_val_sel)
            2'b00: local_enum_var = RED;
            2'b01: local_enum_var = GREEN;
            2'b10: local_enum_var = BLUE;
            default: local_enum_var = RED;
        endcase
        out_enum_int = int'(local_enum_var);
        local_nested_struct_var.nested_struct.member1 = in_struct_val_mem1;
        local_nested_struct_var.nested_struct.member2 = 16'hABCD;
        local_nested_struct_var.nested_struct.member_arr[0] = in_struct_val_arr;
        local_nested_struct_var.nested_struct.member_arr[1] = in_struct_val_arr + 1;
        local_nested_struct_var.nested_struct.member_arr[2] = in_struct_val_arr + 2;
        local_nested_struct_var.nested_member = in_struct_val_arr * 2;
        out_struct_member = local_nested_struct_var.nested_struct.member1;
        out_struct_arr_member = local_nested_struct_var.nested_struct.member_arr[1];
        local_union_var.u_vec = { {24'h0}, in_struct_val_mem1};
        out_struct_member = byte'(local_union_var.u_int);
        local_unpacked_struct_var.u_member1 = in_struct_val_arr;
        local_unpacked_struct_var.u_member2 = in_struct_val_mem1;
        my_void_function(out_struct_member[0], out_void_func_dummy);
    end
endmodule
module mod_operators (
    input logic [7:0] in_op_a,
    input logic [7:0] in_op_b,
    input bit in_op_c,
    output logic [7:0] out_op_arith,
    output bit out_op_logic,
    output logic [3:0] out_op_select,
    output bit out_inside_op
);
    logic [7:0] local_arith;
    bit local_logic;
    logic [7:0] local_vector = 8'hA5;
    int i_loop;
    int loop_limit = 8;
    logic [15:0] local_wide_var;
    always_comb begin @*
        local_arith = in_op_a + in_op_b;
        local_arith = local_arith - 1;
        local_arith = in_op_a * in_op_b;
        if (in_op_b != 0) local_arith = in_op_a / in_op_b;
        if (in_op_b != 0) local_arith = in_op_a % in_op_b;
        out_op_arith = local_arith;
        local_logic = in_op_a > in_op_b;
        local_logic = in_op_a < in_op_b;
        local_logic = in_op_a >= in_op_b;
        local_logic = in_op_a <= in_op_b;
        local_logic = in_op_a == in_op_b;
        local_logic = in_op_a != in_op_b;
        local_logic = in_op_c && local_logic;
        local_logic = in_op_c || local_logic;
        local_logic = !local_logic;
        out_op_logic = local_logic;
        local_vector = in_op_a & in_op_b;
        local_vector = in_op_a | in_op_b;
        local_vector = in_op_a ^ in_op_b;
        local_vector = ~local_vector;
        out_op_select = local_vector[3:0];
        out_op_select[0] = local_vector[7];
        out_op_select[1:0] = local_vector[7-:2];
        out_op_select[1:0] = local_vector[2+:2];
        out_op_arith = in_op_c ? in_op_a : in_op_b;
        local_wide_var = in_op_a;
        loop_block: for (i_loop = 0; i_loop < loop_limit; i_loop = i_loop + 1) begin: loop_block
            if (i_loop == 3) continue;
            if (i_loop == 6) break;
            local_arith[i_loop] = in_op_a[i_loop] ^ in_op_b[i_loop];
        end
        out_inside_op = (in_op_a inside {8'h10, 8'h20, [8'h30:8'h3F]});
        out_op_arith = out_op_arith + local_wide_var[7:0];
    end
endmodule
module mod_procedural_blocks (
    input logic clk,
    input logic reset,
    input logic neg_clk,
    input logic [7:0] in_data,
    input logic [3:0] in_comb,
    output logic [7:0] out_ff_data,
    output logic [3:0] out_comb_data,
    output logic out_negedge_ff,
    output logic out_static_var
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            out_ff_data <= 8'h00;
        end else begin
            out_ff_data <= in_data;
        end
    end
    always_ff @(negedge neg_clk) begin
       out_negedge_ff <= in_comb[1];
    end
    always_comb begin @*
        out_comb_data = in_comb * 2;
    end
    logic local_static_var;
    always begin @(in_comb) 
       local_static_var = in_comb[0];
    end
    assign out_static_var = local_static_var;
endmodule
module mod_case_variations (
    input logic [1:0] in_case_sel,
    input logic [7:0] in_case_data,
    output logic [7:0] out_case_std,
    output logic [7:0] out_casez,
    output logic [7:0] out_case_values
);
    always_comb begin @*
        case (in_case_sel)
            2'b00: out_case_std = in_case_data;
            2'b01: out_case_std = in_case_data + 1;
            2'b10: out_case_std = in_case_data - 1;
            default: out_case_std = 8'hXX;
        endcase; 
        casez (in_case_sel)
            2'b0?: out_casez = in_case_data;
            2'b1?: out_casez = in_case_data + 1;
            default: out_casez = 8'hZZ;
        endcasez; 
        case (in_case_sel)
            2'b00: out_case_values = 0;
            2'b01: out_case_values = 1;
            2'b10: out_case_values = 2;
            2'b11: out_case_values = 3;
            default: out_case_values = 4;
        endcase; 
    end
endmodule
module mod_func_task (
    input int in_ft_arg,
    output int out_func_ret,
    output logic [7:0] out_task_val
);
    function int my_function (input int arg);
        int local_func_var;
        local_func_var = arg * 2;
        return local_func_var;
    endfunction: my_function
    task my_task (input int arg, output logic [7:0] result);
        int temp_arg_plus_5;
        temp_arg_plus_5 = arg + 5;
        result = 8'(temp_arg_plus_5);
    endtask: my_task
    always_comb begin @*
        out_func_ret = my_function(in_ft_arg);
        my_task(in_ft_arg, out_task_val);
    end
endmodule
class SimpleClass;
    int member_val;
    function new(); member_val = 10; endfunction: new
    function virtual void virt_method(); endfunction: virt_method
    function int get_member(); return member_val; endfunction: get_member
    function void set_member(int val); member_val = val; endfunction: set_member
    function void destroy(); endfunction: destroy
endclass: SimpleClass
class ChildClass extends SimpleClass;
    int child_member;
    function new(); super.new(); child_member = 20; endfunction: new
    function virtual void virt_method(); endfunction: virt_method
    function int get_child_member(); return child_member; endfunction: get_child_member
    function void destroy(); super.destroy(); endfunction: destroy
endclass: ChildClass
class ParameterizedClass #(type T=int);
    T data;
    function new(T initial_data); data = initial_data; endfunction: new
endclass: ParameterizedClass
module mod_class_usage (
    input int in_class_val,
    input logic clk,
    input bit in_class_trigger,
    output int out_class_member,
    output int out_class_method,
    output int out_child_class_member,
    output logic out_param_class_dummy
);
    SimpleClass local_class_h;
    ChildClass local_child_class_h;
    ParameterizedClass#(real) local_param_class_h;
    real local_real_val = 3.14;
    bit class_handles_created = 0;
    always_ff @(posedge clk) begin
        if (in_class_trigger && !class_handles_created) begin
            local_class_h = new();
            local_child_class_h = new();
            local_param_class_h = new(local_real_val);
            class_handles_created <= 1;
        end
        if (local_class_h != null) begin
            local_class_h.set_member(in_class_val);
            out_class_member <= local_class_h.member_val;
            out_class_method <= local_class_h.get_member();
            local_class_h.virt_method();
        end else begin
            out_class_member <= 0;
            out_class_method <= 0;
        end
        if (local_child_class_h != null) begin
            out_child_class_member <= local_child_class_h.get_child_member();
            local_child_class_h.virt_method();
            local_child_class_h.destroy();
        end else begin
             out_child_class_member <= 0;
        end
        if (local_param_class_h != null) begin
            out_param_class_dummy <= (local_param_class_h.data > 0);
        end else begin
            out_param_class_dummy <= 0;
        end
    end
endmodule
interface SimpleInterface;
    logic clk;
    logic data_in;
    logic data_out;
    task interface_task(input int arg, output int result);
        result = arg * 2;
    endtask: interface_task
    modport master (
        input clk,
        output data_in,
        input data_out
    );
    modport slave (
        input clk,
        input data_in,
        output data_out
    );
endinterface: SimpleInterface
module mod_interface_usage (
    input logic clk_if_port,
    input int in_if_task_arg,
    output logic out_if_val,
    output int out_if_task_dummy
);
    SimpleInterface simple_if();
    assign simple_if.clk = clk_if_port;
    logic local_if_data_in;
    logic local_if_data_out;
    int task_result;
    always_comb begin @*
       simple_if.master.data_in = local_if_data_in;
       local_if_data_out = simple_if.slave.data_out;
       local_if_data_in = clk_if_port;
       out_if_val = local_if_data_out;
       simple_if.interface_task(in_if_task_arg, task_result);
       out_if_task_dummy = task_result;
    end
endmodule
class RandomClass;
    rand int r_constrained_var;
    rand int r_solve_before_var;
    constraint c_range {
        r_constrained_var > 10;
        r_constrained_var < 100;
        solve r_solve_before_var before r_constrained_var;
    }
    constraint c_even {
        r_constrained_var % 2 == 0;
        disable soft c_even;
    }
    function new(); endfunction: new
endclass: RandomClass
module mod_randomization (
    input bit in_randomize_trigger,
    input logic clk,
    input int in_solve_init,
    output int out_randomized_value,
    output int out_solve_before_value
);
    RandomClass rand_obj;
    bit rand_obj_created = 0;
    always_ff @(posedge clk) begin
        if (in_randomize_trigger && !rand_obj_created) begin
            rand_obj = new();
            rand_obj_created <= 1;
            rand_obj.r_solve_before_var = in_solve_init;
        end
        if (rand_obj != null) begin
            if (rand_obj.randomize()) begin
                 out_randomized_value <= rand_obj.r_constrained_var;
                 out_solve_before_value <= rand_obj.r_solve_before_var;
            end else begin
                 out_randomized_value <= -1;
                 out_solve_before_value <= -1;
            end
        end else begin
             out_randomized_value <= 0;
             out_solve_before_value <= 0;
        end
    end
endmodule
module mod_coverage_assert (
    input bit in_assert_cond,
    input logic [3:0] in_cover_signal,
    output bit out_dummy_coverage
);
    always_comb begin @*
        assert(in_assert_cond);
        cover(in_cover_signal != 4'b0);
        out_dummy_coverage = in_assert_cond;
    end
endmodule
module mod_queue_dynarray_assoc (
    input int in_val,
    input int in_key,
    input bit in_trigger_ff,
    input bit in_trigger_comb,
    input logic clk_ff,
    output int out_dyn_arr_val,
    output int out_queue_val,
    output int out_assoc_arr_val,
    output bit out_stream_dummy,
    output bit out_while_done,
    output bit out_inside_done
);
    int dyn_arr[];
    int queue[$];
    int assoc_arr[int];
    int assoc_arr_from_stream[string];
    int while_counter;
    int inside_check_val = 25;
    always_ff @(posedge clk_ff) begin
        if (in_trigger_ff) begin
            dyn_arr = new[5];
            for (int i = 0; i < 5; i++) dyn_arr[i] <= in_val + i;
            queue = {};
            queue.push_back(in_val + 10);
            queue.push_front(in_val + 11);
            if (!queue.empty()) out_queue_val <= queue.pop_front();
            assoc_arr[in_key] <= in_val + 20;
            if (assoc_arr.exists(in_key)) begin
                out_assoc_arr_val <= assoc_arr[in_key];
            end else begin
                out_assoc_arr_val <= -1;
            end
            if (dyn_arr.size() > 2) out_dyn_arr_val <= dyn_arr[2];
            assoc_arr_from_stream["key"] <= in_val;
            out_stream_dummy <= assoc_arr_from_stream.exists("key");
        end else begin
           out_dyn_arr_val <= 0;
           out_queue_val <= 0;
           out_assoc_arr_val <= 0;
           out_stream_dummy <= 0;
        end
    end
    always_comb begin @*
        out_while_done = 0;
        out_inside_done = 0;
        if (in_trigger_comb) begin
            while_counter = 0;
            while (while_counter < 5) begin
                while_counter++;
            end
            out_while_done = 1;
            if (inside_check_val inside {10, 20, [30:40]}) begin
            end else begin
               out_inside_done = 1;
            end
        end
    end
endmodule
module mod_dpi (
    input int in_dpi_arg,
    output int out_dpi_ret
);
    import "DPI-C" function int dpi_import_func(int arg);
    export "DPI-C" function dpi_export_func;
    function int dpi_export_func(int arg);
        return arg * 3;
    endfunction: dpi_export_func
    int dummy_call_result;
    always_comb begin @*
        out_dpi_ret = dpi_import_func(in_dpi_arg);
        dummy_call_result = dpi_export_func(in_dpi_arg + 1);
        out_dpi_ret = out_dpi_ret + dummy_call_result;
    end
endmodule
module mod_dpi_export_var (
    input int in_val,
    output int out_val
);
    export "DPI-C" var exported_var;
    int exported_var;
    always_comb begin @*
        exported_var = in_val;
        out_val = exported_var + 1;
    end
endmodule
module mod_fork_join (
    input bit in_fork_trigger,
    input logic clk,
    output int out_fork_sum
);
    int task_var1, task_var2, task_var3;
    task my_fork_task1(input int val);
        task_var1 = val + 1;
    endtask: my_fork_task1
    task my_fork_task2(input int val);
        task_var2 = val + 2;
    endtask: my_fork_task2
    task my_fork_task3(input int val);
        task_var3 = val + 3;
    endtask: my_fork_task3
    always_comb begin @*
        task_var1 = 0; task_var2 = 0; task_var3 = 0;
        if (in_fork_trigger) begin
            fork
                my_fork_task1(10);
                my_fork_task2(20);
            join
            fork
                my_fork_task1(100);
                my_fork_task2(200);
            join_any
            fork
                my_fork_task1(1000);
                my_fork_task2(2000);
            join_none
        end
        out_fork_sum = task_var1 + task_var2 + task_var3;
    end
endmodule
module mod_clocking_block (
    input logic clk_cb,
    input logic in_my_input,
    output logic out_cb_dummy,
    output logic out_my_output
);
    clocking cb @(posedge clk_cb);
        default input #1step output #1;
        input my_input;
        output my_output;
    endclocking: cb
    assign cb.my_input = in_my_input;
    assign out_my_output = cb.my_output;
    always_comb begin @*
       out_cb_dummy = out_my_output;
    end
endmodule
module ChildModule (
    input logic child_in,
    output logic child_out
);
    assign child_out = ~child_in;
endmodule: ChildModule
module mod_hierarchy_parent (
    input logic in_hier_val,
    output logic out_hier_val,
    output logic out_child_port
);
    logic parent_to_child;
    logic child_to_parent;
    assign parent_to_child = in_hier_val;
    ChildModule child_inst (
        .child_in(parent_to_child),
        .child_out(child_to_parent)
    );
    assign out_hier_val = child_to_parent;
    assign out_child_port = child_inst.child_out;
endmodule: mod_hierarchy_parent
module mod_attribute (
    input logic [1:0] in_attr_sel,
    output logic out_attr_val
);
    logic local_case_val;
    (* full_case *)
    always_comb begin @*
        case (in_attr_sel)
            2'b00: local_case_val = 1'b0;
            2'b01: local_case_val = 1'b1;
            2'b10: local_case_val = 1'b0;
            2'b11: local_case_val = 1'b1;
            default: local_case_val = 1'b0;
        endcase
        out_attr_val = local_case_val;
    end
endmodule
package my_package;
    parameter PKG_PARAM = 5;
    function int pkg_function(input int val);
        return val + PKG_PARAM;
    endfunction: pkg_function
    export my_package::PKG_PARAM;
    export my_package::pkg_function;
endpackage: my_package
module mod_package_usage (
    input int in_pkg_val,
    output int out_pkg_func_ret,
    output int out_pkg_param
);
    import my_package::*;
    always_comb begin @*
        out_pkg_func_ret = pkg_function(in_pkg_val);
        out_pkg_param = my_package::PKG_PARAM;
    end
endmodule
module mod_generate (
    input bit in_gen_en,
    input logic [1:0] in_gen_select,
    output logic [7:0] out_gen_val
);
    logic [7:0] gen_result_0, gen_result_1;
    generate
        if (in_gen_en) begin : gen_if_block
            assign gen_result_0 = 8'hAA;
        end else begin
            assign gen_result_0 = 8'h55;
        end
        gen_for_block: for (genvar i = 0; i < 2; i++) begin : gen_for_block
            if (i == 0) assign gen_result_1 = 8'h11;
            else assign gen_result_1 = 8'h22;
        end
    endgenerate
    always_comb begin @*
        case(in_gen_select)
            2'b00: out_gen_val = gen_result_0;
            2'b01: out_gen_val = gen_result_1;
            default: out_gen_val = 8'hZZ;
        endcase
    end
endmodule
program mod_program_block (
    input bit in_prog,
    output bit out_prog
);
    int dummy_prog_var;
    always_comb begin @*
        dummy_prog_var = in_prog;
        out_prog = dummy_prog_var;
    end
endprogram: mod_program_block
module mod_more_types (
    input logic in_sc_logic,
    input logic [31:0] in_sc_bv,
    input int in_sample_val,
    output logic out_sc_logic,
    output logic [31:0] out_sc_bv,
    output int out_sample_val_peek
);
    logic local_sc_logic_var;
    logic [31:0] local_sc_bv_var;
    sample_queue local_sample_queue;
    always_comb begin @*
        local_sc_logic_var = in_sc_logic;
        local_sc_bv_var = in_sc_bv;
        out_sc_logic = local_sc_logic_var;
        out_sc_bv = local_sc_bv_var;
        local_sample_queue.push_back(in_sample_val);
        if (!local_sample_queue.empty()) begin
            out_sample_val_peek = local_sample_queue.front();
        end else begin
            out_sample_val_peek = 0;
        end
    end
endmodule
module mod_types_strength_attr (
    input bit in_sel,
    output bit out_val,
    output logic [31:0] out_sc_bv_val,
    output int out_static
);
    tri0 (supply0, supply1) tri0_net;
    tri1 (pull1, pull0) tri1_net;
    logic (* public *) pub_sig;
    logic [31:0] (* sc_bv *) sc_bv_sig;
    static int static_var = 10;
    assign tri0_net = 1'b0;
    assign tri1_net = 1'b1;
    assign pub_sig = in_sel;
    assign sc_bv_sig = {31'b0, in_sel};
    always_comb begin @*
        out_val = tri0_net ^ tri1_net ^ pub_sig;
        out_sc_bv_val = sc_bv_sig;
        out_static = static_var;
    end
endmodule
module mod_params_range #(
    parameter int INT_PARAM = 10,
    parameter real REAL_PARAM = 3.14,
    parameter string STR_PARAM = "hello",
    parameter int RANGE_PARAM = 4,
    parameter int ASC_RANGE_L = 0,
    parameter int ASC_RANGE_R = 3
) (
    input int in_val,
    output int out_param_int,
    output real out_param_real,
    output string out_param_string,
    output logic [RANGE_PARAM-1:0] out_ranged_wire_desc,
    output logic [ASC_RANGE_L:ASC_RANGE_R] out_ranged_wire_asc
);
    logic [RANGE_PARAM-1:0] ranged_wire_desc;
    logic [ASC_RANGE_L:ASC_RANGE_R] ranged_wire_asc;
    always_comb begin @*
        out_param_int = INT_PARAM + in_val;
        out_param_real = REAL_PARAM + $real(in_val);
        out_param_string = STR_PARAM;
        ranged_wire_desc = {>>{in_val}};
        out_ranged_wire_desc = ranged_wire_desc;
        ranged_wire_asc = {<<{in_val}};
        out_ranged_wire_asc = ranged_wire_asc;
    end
endmodule
module mod_unroll_attr (
    input int loop_limit,
    output int out_sum
);
    int sum = 0;
    int i;
    always_comb begin @*
        sum = 0;
        (* unroll_full *)
        for (i = 0; i < loop_limit; i++) begin
            sum = sum + i;
        end
        (* unroll_disable *)
        while (sum < 100) begin
            sum = sum + 1;
            if (sum > 50) break;
        end
        out_sum = sum;
    end
endmodule
module mod_multidim_unpacked (
    input int in_val,
    output int out_val
);
    int multi_arr [0:1][0:2][0:3];
    always_comb begin @*
        for (int i = 0; i < 2; i++) begin
            for (int j = 0; j < 3; j++) begin
                for (int k = 0; k < 4; k++) begin
                    multi_arr[i][j][k] = in_val + i*100 + j*10 + k;
                end
            end
        end
        out_val = multi_arr[1][2][3];
    end
endmodule
module mod_explicit_timescale (
    input bit in_val,
    output bit out_val
);
    always_comb assign out_val = in_val;
endmodule: mod_explicit_timescale
module mod_sample_queue_ff (
    input int in_val,
    input bit in_trigger_push,
    input bit in_trigger_pop,
    input logic clk,
    output int out_val_pop
);
    sample_queue local_sample_queue;
    always_ff @(posedge clk) begin
        if (in_trigger_push) begin
            local_sample_queue.push_back(in_val);
        end
        if (in_trigger_pop) begin
            if (!local_sample_queue.empty()) begin
                out_val_pop <= local_sample_queue.pop_front();
            end else begin
                out_val_pop <= 0;
            end
        end else begin
            out_val_pop <= 0;
        end
    end
endmodule

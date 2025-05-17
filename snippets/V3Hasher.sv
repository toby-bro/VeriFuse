interface dummy_if;
    logic sig;
    task automatic my_task();
        sig = 1'b1;
    endtask
    function automatic int my_func();
        return 123;
    endfunction
    modport mp (output sig, export task my_task, export function my_func);
endinterface
class dummy_class;
    int data = 42;
    function automatic int get_data(); return data; endfunction
endclass
class base_class;
    int base_data = 1;
    function automatic int get_base_data(); return base_data; endfunction
endclass
class derived_class extends base_class;
    int derived_data = 2;
    function automatic int get_derived_data(); return derived_data + get_base_data(); endfunction
endclass
class nullable_class;
    int data;
endclass
class my_class_with_task;
    int data = 10;
    task automatic process_data(input int val, output int result);
        data = data + val;
        result = data * 2;
    endtask
endclass
class SelfReferencingClass;
    int my_data = 5;
    function automatic int get_my_data();
        return this.my_data;
    endfunction
endclass
package my_package;
    logic pkg_var = 1'b0;
endpackage : my_package
package my_second_package;
    int pkg2_data = 500;
endpackage : my_second_package
module basic_types_module(
    input logic in_logic,
    input bit in_bit,
    input byte in_byte,
    output logic out_logic,
    output bit out_bit,
    output byte out_byte
);
    int internal_int;
    longint internal_longint;
    integer internal_integer;
    time internal_time_type;
    chandle internal_chandle_type;
    real internal_real;
    shortreal internal_shortreal;
    string internal_string;
    assign out_logic = in_logic;
    assign out_bit = in_bit;
    assign out_byte = in_byte;
    always_comb begin
        internal_int = in_byte;
        internal_longint = 1234567890123456789;
        internal_integer = 5000;
        internal_real = 3.14;
        internal_shortreal = 1.0;
        internal_string = "hello";
    end
endmodule
module packed_arrays_ranges_module(
    input logic [7:0] in_packed_byte,
    input bit [31:0] in_packed_word,
    input int in_range_index,
    output logic [7:0] out_packed_byte,
    output bit [15:0] out_packed_halfword,
    output logic [3:0] out_dynamic_slice
);
    logic [7:0] temp_byte;
    bit [31:0] temp_word;
    logic [63:0] large_reg = {in_packed_word, in_packed_word};
    logic [3:0] dynamic_slice;
    assign temp_byte = in_packed_byte;
    assign temp_word = in_packed_word;
    assign out_packed_byte = temp_byte;
    assign out_packed_halfword = temp_word[31:16];
    always_comb begin
        dynamic_slice = large_reg[in_range_index*4 +: 4];
        out_dynamic_slice = dynamic_slice;
    end
endmodule
module unpacked_struct_enum_module(
    input logic in_flag,
    input int init_index,
    output logic out_flag_reverse,
    output logic [7:0] out_data_byte
);
    typedef enum { IDLE, START, DONE } state_e;
    typedef struct packed {
        logic [7:0] addr;
        logic [31:0] data;
        logic write;
    } bus_s;
    state_e current_state = IDLE;
    bus_s request = '{addr: 8'h11, data: 32'hFFEEFFEE, write: 1'b0};
    logic [0:3][7:0] data_bytes_unpacked = {'hA, 'hB, 'hC, 'hD};
    assign out_flag_reverse = ~in_flag;
    always_comb begin
        request.addr = 8'hFF;
        current_state = in_flag ? START : IDLE;
        if (init_index >= 0 && init_index < 4) data_bytes_unpacked[init_index] = request.addr;
        out_data_byte = (init_index >= 0 && init_index < 4) ? data_bytes_unpacked[init_index] : 8'h0;
    end
endmodule
module collections_refined_module(
    input int in_key,
    input int in_value,
    input int in_index,
    input logic push_queue,
    input logic pop_queue,
    input logic delete_assoc,
    output int out_assoc_value,
    output int out_queue_size,
    output int out_dyn_size,
    output int out_first_key_exists
);
    logic [string] assoc_array = '{"init_key1": 100, "init_key2": 200};
    int queue_q [$] = {1, 2, 3};
    int dyn_array [] = {5, 6, 7, 8};
    string dynamic_key;
    string first_key;
    always_comb begin
        dynamic_key = $sformatf("key%0d", in_key);
        assoc_array[dynamic_key] = in_value;
        if (assoc_array.exists(dynamic_key)) begin
            out_assoc_value = assoc_array[dynamic_key];
        end else begin
            out_assoc_value = 0;
        end
        if (delete_assoc && assoc_array.exists(dynamic_key)) begin
           assoc_array.delete(dynamic_key);
        end
        if (assoc_array.first(first_key)) begin
            out_first_key_exists = 1;
        end else begin
            out_first_key_exists = 0;
        end
        if (push_queue) begin
            queue_q.push_back(in_index);
        end
        if (pop_queue && queue_q.size() > 0) begin
           void'(queue_q.pop_front());
        end
        out_queue_size = queue_q.size();
        if (in_index >= 0 && in_index < 10) begin
           dyn_array = new[in_index];
           if (in_index > 0 && in_index < dyn_array.size()) dyn_array[0] = in_value;
        end else if (in_index < 0 && dyn_array != null) begin
           dyn_array = null;
        end
        out_dyn_size = (dyn_array != null) ? dyn_array.size() : 0;
    end
endmodule
module procedural_logic_module(
    input logic [1:0] in_sel,
    input logic [7:0] in_data_a,
    input logic [7:0] in_data_b,
    input logic condition,
    output logic [7:0] out_data,
    output logic [7:0] out_conditional
);
    logic [7:0] temp_result;
    always_comb begin
        temp_result = 8'h00;
        if (in_sel == 2'b00) begin
            temp_result = in_data_a + in_data_b;
        end else begin
            case (in_sel)
                2'b01: temp_result = in_data_a & in_data_b;
                2'b10: temp_result = in_data_a | in_data_b;
                default: temp_result = in_data_a ^ in_data_b;
            endcase
        end
        out_data = temp_result;
        out_conditional = condition ? in_data_a : in_data_b;
    end
endmodule
module sequential_logic_module(
    input logic clk,
    input logic rst,
    input logic [15:0] data_in,
    output logic [15:0] data_out
);
    logic [15:0] state;
    always_ff @(posedge clk or negedge rst) begin
        if (~rst) begin
            state <= 16'h0000;
        end else begin
            state <= data_in;
        end
    end
    assign data_out = state;
endmodule
module functions_tasks_module(
    input int func_in_int,
    input logic [7:0] task_in_a,
    input logic [7:0] task_in_b,
    input int recursion_depth,
    output int func_out_int,
    output logic [7:0] task_out_sum,
    output logic recursion_done
);
    logic [7:0] internal_sum;
    logic recursive_task_done;
    function automatic int factorial_recursive(input int n);
        if (n <= 1) return 1;
        return n * factorial_recursive(n - 1);
    endfunction
    task automatic add_bytes(input logic [7:0] a, input logic [7:0] b, output logic [7:0] sum);
        sum = a + b;
    endtask
    task automatic recursive_task(input int depth);
        if (depth > 0) begin
            recursive_task(depth - 1);
        end else begin
            recursive_task_done = 1'b1;
        end
    endtask
    assign func_out_int = factorial_recursive(func_in_int % 5);
    always_comb begin
        add_bytes(task_in_a, task_in_b, internal_sum);
        task_out_sum = internal_sum;
        recursive_task_done = 1'b0;
        recursive_task(recursion_depth % 3);
        recursion_done = recursive_task_done;
    end
endmodule
module dpi_module(
    input int dpi_in_int,
    input string dpi_in_string,
    output real dpi_out_real,
    output int dpi_out_int
);
    real internal_dpi_real;
    int internal_dpi_int;
    import "DPI-C" function void c_void_func(input int arg1, output real arg2);
    import "DPI-C" function int c_int_func(input string s);
    always_comb begin
        internal_dpi_real = 0.0; 
        internal_dpi_int = 0; 
        dpi_out_real = internal_dpi_real;
        dpi_out_int = internal_dpi_int;
    end
endmodule
module loops_params_module(
    input logic [7:0] input_byte,
    input int loop_limit,
    output logic [7:0] output_sum_byte
);
    parameter MAX_ITERATIONS = 10;
    localparam DEFAULT_SUM = 8'h00;
    logic [7:0] sum_bytes = DEFAULT_SUM;
    (* custom_attr = "value" *) logic attributed_reg;
    (* keep *) logic another_attributed_signal;
    always_comb begin
        sum_bytes = 8'h00;
        for (int i = 0; i < ((loop_limit < MAX_ITERATIONS) ? loop_limit : MAX_ITERATIONS); i++) begin : for_loop_name
            sum_bytes = sum_bytes + input_byte;
        end
        output_sum_byte = sum_bytes;
        attributed_reg = (sum_bytes != 8'h00);
        another_attributed_signal = attributed_reg;
    end
endmodule
module scopes_module(
    input logic [7:0] outer_input,
    output logic [7:0] inner_output
);
    logic [7:0] outer_var;
    always_comb begin
        logic [7:0] middle_var;
        outer_var = outer_input;
        middle_var = outer_var + 1;
        begin
            logic [7:0] inner_var;
            inner_var = middle_var * 2;
            inner_output = inner_var;
        end
    end
endmodule
module class_interface_ref_module(
    input dummy_if.mp in_if_mp,
    output logic out_sig,
    output int out_data
);
    dummy_class internal_class_inst;
    int temp_data;
    assign out_sig = in_if_mp.sig;
    always_comb begin
        if (internal_class_inst == null) begin
            internal_class_inst = new();
        end
        in_if_mp.my_task();
        temp_data = in_if_mp.my_func();
        if (internal_class_inst != null) begin
           internal_class_inst.data = 99;
           temp_data = internal_class_inst.get_data();
        end else begin
           temp_data = 0;
        end
        out_data = temp_data;
    end
endmodule
module assertions_covers_module(
    input logic assertion_condition,
    input logic cover_condition,
    input logic clk,
    output logic assertion_feedback
);
    (* my_general_attribute = "test" *) logic attributed_var1;
    (* trace = "on" *) logic traced_signal;
    (* coverage_point = "enabled" *) logic cover_point_signal;
    assert property (@(posedge clk) assertion_condition |-> !assertion_feedback);
    cover property (@(posedge clk) cover_condition);
    cp_coverpoint : coverpoint (cover_point_signal);
    always_comb begin
        attributed_var1 = assertion_condition;
        traced_signal = cover_condition;
        cover_point_signal = assertion_condition && cover_condition;
        assertion_feedback = !assertion_condition;
    end
endmodule
module typedef_fwd_paramtype_module(
    input int in_int,
    output logic out_bit
);
    parameter type P_TYPE = int;
    P_TYPE param_typed_var = 10;
    typedef logic my_logic_t;
    typedef my_logic_t my_other_logic_t;
    my_logic_t internal_logic = 1'b1;
    my_other_logic_t another_internal_logic;
    assign out_bit = internal_logic;
    always_comb begin
        another_internal_logic = internal_logic;
        if (param_typed_var > 5) begin
            internal_logic = ~internal_logic;
        end
    end
endmodule
module stream_void_const_module(
    input logic [31:0] in_data,
    input logic [7:0] in_byte_array [0:3],
    output logic [31:0] out_data_streamed,
    output logic out_void_called
);
    const logic [7:0] CONST_BYTE = 8'hAB;
    function automatic void set_output_flag(output logic flag);
        flag = 1'b1;
    endfunction
    logic [31:0] streamed_bytes;
    logic void_flag;
    assign streamed_bytes = {>>{in_byte_array}};
    always_comb begin
        void_flag = 1'b0;
        set_output_flag(void_flag);
        if ($bits(in_data) >= 8 && in_data[7:0] == CONST_BYTE) begin
             set_output_flag(void_flag);
        end
    end
    assign out_void_called = void_flag;
    assign out_data_streamed = streamed_bytes;
endmodule
module class_extends_module(
    input int in_val,
    output int out_total_data
);
    derived_class inst_derived;
    int result_data;
    always_comb begin
        if (inst_derived == null) begin
           inst_derived = new();
        end
        result_data = 0;
        if (inst_derived != null) begin
             inst_derived.derived_data = in_val;
             result_data = inst_derived.get_derived_data();
        end
        out_total_data = result_data;
    end
endmodule
module null_check_module(
    input logic enable_check,
    output logic is_null_out
);
    nullable_class my_handle;
    always_comb begin
        if (enable_check && my_handle == null) begin
            my_handle = new();
        end else if (!enable_check && my_handle != null) begin
            my_handle = null;
        end
        if (my_handle == null) begin
            is_null_out = 1'b1;
        end else begin
            is_null_out = 1'b0;
        end
    end
endmodule
module ccast_module(
    input logic [31:0] in_word,
    output logic [7:0] out_byte_cast
);
    logic [7:0] byte_val = (logic [7:0])in_word;
    assign out_byte_cast = byte_val;
endmodule
module varxref_module(
    input logic in_flag,
    output logic out_pkg_var
);
    logic local_var;
    always_comb begin
        local_var = in_flag;
        my_package::pkg_var = local_var;
        out_pkg_var = my_package::pkg_var;
    end
endmodule
module sensitivity_list_module(
    input logic clk,
    input logic reset,
    input logic data_in_edge,
    input logic data_in_level,
    output logic data_out_edge,
    output logic data_out_level
);
    logic edge_triggered_reg;
    logic level_sensitive_var;
    always_ff @(posedge clk, negedge reset) begin
        if (!reset) begin
            edge_triggered_reg <= 1'b0;
        end else begin
            edge_triggered_reg <= data_in_edge;
        end
    end
    always_comb begin
        level_sensitive_var = data_in_level;
    end
    always_comb begin
       data_out_level = data_in_level;
    end
    assign data_out_edge = edge_triggered_reg;
endmodule
module pragma_module(
    input logic in_data,
    output logic out_data
);
    (* verilator_public *) logic public_signal;
    (* fsm_encoding = "one-hot" *) logic [1:0] fsm_state;
    (* full_case *) (* parallel_case *) case (fsm_state)
        2'b01: ;
        2'b10: ;
        default: ;
    endcase
    always_comb begin
        public_signal = in_data;
        fsm_state = in_data ? 2'b01 : 2'b10;
        out_data = public_signal || |fsm_state;
    end
endmodule
module range_slice_module(
    input logic [63:0] in_large_word,
    input int in_index,
    output logic [7:0] out_byte_slice,
    output logic [3:0] out_part_select
);
    logic [63:0] temp_word = in_large_word;
    logic [7:0] byte_slice;
    logic [3:0] part_select;
    always_comb begin
        byte_slice = temp_word[15:8];
        part_select = temp_word[in_index % 61 +: 4];
        out_byte_slice = byte_slice;
        out_part_select = part_select;
    end
endmodule
module typedef_fwd_module_added(
    input logic in_flag,
    output logic out_valid
);
    typedef struct forward my_fwd_struct_name_t;
    typedef struct {
        int data;
        logic valid;
    } my_fwd_struct_name_t;
    my_fwd_struct_name_t my_struct_var;
    always_comb begin
        my_struct_var.data = in_flag ? 100 : 0;
        my_struct_var.valid = in_flag;
        out_valid = my_struct_var.valid;
    end
endmodule
module func_handle_module(
    input int in_val,
    output int out_val
);
    function automatic int my_local_func(input int a);
        return a + 1;
    endfunction
    typedef function int (*int_func_ptr)(int);
    int_func_ptr func_h;
    int result;
    always_comb begin
        func_h = my_local_func;
        if (func_h != null) begin
            result = func_h(in_val);
        end else begin
            result = 0;
        end
        out_val = result;
    end
endmodule
module static_var_scope_module(
    input int in_incr,
    output int out_val
);
    task automatic my_task();
        static int counter = 0;
        counter += in_incr;
    endtask
    int current_counter;
    always_comb begin
        my_task();
        current_counter = my_task::counter;
        out_val = current_counter;
    end
endmodule
module package_import_module(
    input int in_val,
    output logic out_val_pkg1,
    output int out_val_pkg2
);
    import my_package::*;
    import my_second_package::pkg2_data;
    always_comb begin
        my_package::pkg_var = (in_val > 100) ? 1'b1 : 1'b0;
        out_val_pkg1 = my_package::pkg_var;
        pkg2_data = in_val + pkg2_data;
        out_val_pkg2 = pkg2_data;
    end
endmodule
module sscanf_module(
    input string in_string,
    input logic [7:0] pattern_val,
    output int out_int_val,
    output real out_real_val,
    output logic [7:0] out_byte_val
);
    string pattern_str;
    int temp_int;
    real temp_real;
    logic [7:0] temp_byte;
    always_comb begin
        pattern_str = "%d %f %h";
        temp_int = 0; 
        temp_real = 0.0; 
        temp_byte = 8'h0; 
        out_int_val = temp_int; 
        out_real_val = temp_real; 
        out_byte_val = temp_byte + pattern_val;
    end
endmodule
module class_method_task_module(
    input int in_value,
    output int out_result
);
    my_class_with_task inst_task_class;
    int temp_result;
    always_comb begin
        if (inst_task_class == null) begin
            inst_task_class = new();
        end
        temp_result = 0;
        if (inst_task_class != null) begin
            inst_task_class.process_data(in_value, temp_result);
        end
        out_result = temp_result;
    end
endmodule
module fscanf_module(
    input logic [31:0] in_dummy_data,
    output int out_scan_count
);
    int scanned_int;
    string scanned_string;
    real scanned_real;
    always_comb begin
        scanned_int = 0; 
        scanned_string = ""; 
        scanned_real = 0.0; 
        out_scan_count = 0; 
    end
endmodule
module event_jump_module(
    input logic trigger_event,
    output logic event_triggered_out
);
    event my_event;
    logic event_flag = 1'b0;
    always @(my_event) begin : event_watcher
        event_flag = 1'b1;
    end
    always_comb begin
        if (trigger_event) begin
            -> my_event;
        end
    end
    assign event_triggered_out = event_flag;
endmodule
module await_module(
    input logic clk,
    input logic condition_in,
    output logic await_triggered
);
    logic internal_await_flag = 1'b0;
    always @(posedge clk) begin
        await(condition_in) begin
            internal_await_flag = 1'b1;
        end
    end
    assign await_triggered = internal_await_flag;
endmodule
module generate_module(
    input int gen_limit,
    input logic [7:0] input_value,
    output logic [7:0] output_sum
);
    parameter MAX_GEN = 4;
    logic [7:0] partial_values [MAX_GEN];
    logic [7:0] sum_stages [MAX_GEN];
    genvar i;
    for (i = 0; i < MAX_GEN; i=i+1) begin : gen_loop
        always_comb begin
            if (i < gen_limit && i < MAX_GEN) begin
                partial_values[i] = input_value;
            end else begin
                partial_values[i] = 8'h0;
            end
        end
        always_comb begin
            if (i == 0) begin
                sum_stages[i] = partial_values[i];
            end else begin
                sum_stages[i] = sum_stages[i-1] + partial_values[i];
            end
        end
    end
    assign output_sum = (MAX_GEN > 0) ? sum_stages[MAX_GEN - 1] : 8'h0;
endmodule
module self_reference_module(
    input int in_dummy,
    output int out_data
);
    SelfReferencingClass inst;
    int data_val;
    always_comb begin
        if (inst == null) begin
            inst = new();
        end
        data_val = 0;
        if (inst != null) begin
            data_val = inst.get_my_data();
        end
        out_data = data_val + in_dummy;
    end
endmodule
module error_warning_info_module(
    input logic trigger_error,
    input logic trigger_warning,
    input logic trigger_info,
    output logic out_dummy
);
    always_comb begin
    end
    assign out_dummy = trigger_error || trigger_warning || trigger_info;
endmodule
module numeric_literals_module(
    input logic [7:0] in_byte,
    output logic [15:0] out_sum,
    output real out_real
);
    logic [15:0] hex_val = 16'hABCD;
    logic [11:0] bin_val = 12'b101_0110_1110;
    int dec_val = 32'd12345;
    real pi_val = 3.14159;
    logic [7:0] sized_byte = 8'b11110000;
    logic [7:0] single_quote_byte = 'hEE;
    always_comb begin
        out_sum = hex_val + bin_val + dec_val + sized_byte + single_quote_byte + in_byte;
        out_real = pi_val;
    end
endmodule
module simple_initializer_module(
    input int in_val,
    output int out_sum
);
    int initialized_var = 10;
    logic [7:0] initialized_packed = 8'h55;
    int initialized_array [2] = '{1, 2};
    always_comb begin
        out_sum = initialized_var + initialized_packed + initialized_array[0] + initialized_array[1] + in_val;
    end
endmodule
module monitor_module(
    input logic enable_monitor_on,
    input logic enable_monitor_off,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    always_comb begin
    end
    assign data_out = data_in;
endmodule

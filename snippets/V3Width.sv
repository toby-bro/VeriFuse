module arith_ops (
    input signed [7:0] i_signed_8,
    input unsigned [15:0] i_unsigned_16,
    input real i_real_in_1,
    input real i_real_in_2,
    output signed [16:0] o_add_s,
    output unsigned [15:0] o_sub_u,
    output [23:0] o_mul,
    output signed [7:0] o_div_s,
    output [7:0] o_mod,
    output [15:0] o_and,
    output signed [15:0] o_or_s,
    output [7:0] o_xor,
    output wire o_red_and,
    output wire o_red_or,
    output wire o_red_xor,
    output wire o_one_hot,
    output wire o_one_hot0,
    output wire o_is_unknown,
    output wire o_log_not,
    output wire o_log_and,
    output wire o_log_or,
    output wire o_log_eq,
    output wire o_log_if,
    output signed [7:0] o_negate_s,
    output [15:0] o_not,
    output real o_add_r,
    output real o_sub_r,
    output real o_mul_r,
    output real o_div_r,
    output real o_pow_r,
    output real o_negate_r,
    output wire o_cmp_eq,
    output wire o_cmp_neq,
    output wire o_cmp_gt,
    output wire o_cmp_gte,
    output wire o_cmp_lt,
    output wire o_cmp_lte,
    output wire o_cmp_eq_case,
    output wire o_cmp_neq_case,
    output wire o_cmp_eq_wild,
    output wire o_cmp_neq_wild,
    output wire o_cmp_gt_s,
    output wire o_cmp_lt_s,
    output wire o_cmp_real_eq,
    output wire o_cmp_real_gt
);
    assign o_add_s = i_signed_8 + i_unsigned_16;
    assign o_sub_u = i_unsigned_16 - i_signed_8;
    assign o_mul = i_unsigned_16 * i_signed_8;
    assign o_div_s = i_signed_8 / 4;
    assign o_mod = i_unsigned_16 % 8;
    assign o_and = i_unsigned_16 & 16'hF0F0;
    assign o_or_s = i_signed_8 | 8'h55;
    assign o_xor = i_signed_8 ^ 8'hAA;
    assign o_red_and = &i_unsigned_16;
    assign o_red_or = |i_signed_8;
    assign o_red_xor = ^i_unsigned_16;
    assign o_one_hot = i_unsigned_16.onehot();
    assign o_one_hot0 = i_unsigned_16.onehot0();
    assign o_is_unknown = i_unsigned_16.isunknown();
    assign o_log_not = !i_unsigned_16;
    assign o_log_and = (i_signed_8 > 0) && (i_unsigned_16 < 100);
    assign o_log_or = (i_signed_8 == -1) || (i_unsigned_16 == 50);
    assign o_log_eq = (i_signed_8 > 0) == (i_unsigned_16 < 100);
    assign o_log_if = (i_signed_8 > 0) ? (i_unsigned_16 < 100) : (i_unsigned_16 == 50);
    assign o_negate_s = -i_signed_8;
    assign o_not = ~i_unsigned_16;
    assign o_add_r = i_real_in_1 + i_real_in_2;
    assign o_sub_r = i_real_in_1 - i_real_in_2;
    assign o_mul_r = i_real_in_1 * i_real_in_2;
    assign o_div_r = i_real_in_1 / i_real_in_2;
    assign o_pow_r = i_real_in_1 ** 2.0;
    assign o_negate_r = -i_real_in_1;
    assign o_cmp_eq = i_signed_8 == i_unsigned_16;
    assign o_cmp_neq = i_signed_8 != i_unsigned_16;
    assign o_cmp_gt = i_unsigned_16 > i_signed_8;
    assign o_cmp_gte = i_unsigned_16 >= i_signed_8;
    assign o_cmp_lt = i_signed_8 < i_unsigned_16;
    assign o_cmp_lte = i_signed_8 <= i_unsigned_16;
    assign o_cmp_eq_case = i_unsigned_16 === 16'bZ;
    assign o_cmp_neq_case = i_unsigned_16 !== 16'bx;
    assign o_cmp_eq_wild = i_unsigned_16 ==? 16'b1100_11??_ZZZZ_????;
    assign o_cmp_neq_wild = i_unsigned_16 !=? 16'b1100_11??_ZZZZ_????;
    assign o_cmp_gt_s = $signed(i_unsigned_16) > i_signed_8;
    assign o_cmp_lt_s = i_signed_8 < $signed(i_unsigned_16);
    assign o_cmp_real_eq = i_real_in_1 == i_real_in_2;
    assign o_cmp_real_gt = i_real_in_1 > i_real_in_2;
endmodule
module shift_ops (
    input [7:0] i_data,
    input [3:0] i_shift_count,
    output [7:0] o_shift_l,
    output [7:0] o_shift_r,
    output signed [7:0] o_shift_rs
);
    assign o_shift_l = i_data << i_shift_count;
    assign o_shift_r = i_data >> i_shift_count;
    assign o_shift_rs = $signed(i_data) >>> i_shift_count;
endmodule
module conditional_op (
    input i_cond,
    input [7:0] i_true_int,
    input [15:0] i_false_int,
    input real i_true_real,
    input real i_false_real,
    output [15:0] o_int_cond,
    output real o_real_cond
);
    assign o_int_cond = i_cond ? i_true_int : i_false_int;
    assign o_real_cond = i_cond ? i_true_real : i_false_real;
endmodule
module concat_repl (
    input [3:0] i_a,
    input [4:0] i_b,
    output [12:0] o_concat,
    output [15:0] o_repl
);
    assign o_concat = {i_a, i_b, 4'hF};
    assign o_repl = {4{i_a}};
endmodule
module selects (
    input [31:0] i_vec,
    input [7:0] i_array [0:3],
    input [1:0] i_bit_index,
    input [3:0] i_array_index_const,
    input int i_array_index_var,
    output wire o_bit_select_const,
    output wire o_bit_select_var,
    output [7:0] o_part_select_const,
    output [7:0] o_part_select_plus,
    output [7:0] o_part_select_minus,
    output [7:0] o_array_select_const,
    output [7:0] o_array_select_var,
    output reg [7:0] o_array_select_var_proc
);
    assign o_bit_select_const = i_vec[5];
    assign o_bit_select_var = i_vec[i_bit_index];
    assign o_part_select_const = i_vec[15:8];
    assign o_part_select_plus = i_vec[i_bit_index +: 8];
    assign o_part_select_minus = i_vec[i_bit_index -: 8];
    assign o_array_select_const = i_array[i_array_index_const];
    assign o_array_select_var = i_array[i_array_index_var];
    always_comb begin
        o_array_select_var_proc = i_array[i_array_index_var];
    end
endmodule
module array_types (
    input int i_assoc_key,
    input [7:0] i_assoc_value,
    input string i_wildcard_key,
    input [15:0] i_wildcard_value,
    input int i_dyn_size,
    input int i_queue_size,
    input [7:0] i_unpacked_array_in [0:1],
    input [7:0] i_dyn_array_in [],
    input [7:0] i_queue_in [$],
    output logic [7:0] o_unpacked_array_out [0:1],
    output logic [7:0] o_dyn_array_out [],
    output logic [7:0] o_queue_out [$],
    output logic [7:0] o_assoc_out,
    output logic [15:0] o_wildcard_out
);
    logic [7:0] unpacked_array [0:1];
    logic [7:0] dyn_array [];
    logic [7:0] queue [$];
    logic [7:0] assoc_array [int];
    logic [15:0] wildcard_array [string];
    assign unpacked_array = i_unpacked_array_in;
    always_comb begin
        dyn_array = i_dyn_array_in;
        queue = i_queue_in;
        assoc_array[i_assoc_key] = i_assoc_value;
        wildcard_array[i_wildcard_key] = i_wildcard_value;
        o_assoc_out = assoc_array[i_assoc_key];
        o_wildcard_out = wildcard_array[i_wildcard_key];
        o_unpacked_array_out = unpacked_array;
        o_dyn_array_out = dyn_array;
        o_queue_out = queue;
    end
    logic [7:0] unpacked_slice [0:0];
    assign unpacked_slice = unpacked_array[1:1];
endmodule
module struct_union (
    input [15:0] i_packed_struct_in,
    input [7:0] i_struct_member_a,
    input int i_struct_member_b,
    output [15:0] o_packed_struct_out,
    output int o_unpacked_struct_member_b,
    output [7:0] o_unpacked_struct_member_a
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } packed_struct_t;
    typedef struct {
        logic [7:0] member_a;
        int member_b;
    } unpacked_struct_t;
    packed_struct_t packed_struct_var;
    unpacked_struct_t unpacked_struct_var;
    assign packed_struct_var = i_packed_struct_in;
    assign o_packed_struct_out = packed_struct_var;
    always_comb begin
        unpacked_struct_var.member_a = i_struct_member_a;
        unpacked_struct_var.member_b = i_struct_member_b;
        o_unpacked_struct_member_a = unpacked_struct_var.member_a;
        o_unpacked_struct_member_b = unpacked_struct_var.member_b;
    end
    typedef union packed {
        logic [15:0] word;
        logic [7:0] byte_field [1:0];
    } packed_union_t;
    packed_union_t packed_union_var;
endmodule
module enum_type (
    input int i_enum_value,
    input int i_next_prev_step,
    output logic [1:0] o_enum_val,
    output string o_enum_name,
    output logic [1:0] o_enum_next,
    output logic [1:0] o_enum_prev,
    output int o_enum_num,
    output logic [1:0] o_enum_first,
    output logic [1:0] o_enum_last
);
    typedef enum {
        RED, GREEN, BLUE
    } color_t;
    color_t color_var;
    always_comb begin
        color_var = color_t'(i_enum_value);
        o_enum_val = color_var;
        o_enum_name = color_var.name();
        o_enum_next = color_var.next(i_next_prev_step);
        o_enum_prev = color_var.prev(i_next_prev_step);
        o_enum_num = color_t::num();
        o_enum_first = color_t::first();
        o_enum_last = color_t::last();
    end
endmodule
module typedef_ref (
    input [7:0] i_data,
    output t_my_type o_data_typed
);
    typedef logic [7:0] t_my_type;
    t_my_type my_var;
    assign my_var = i_data;
    assign o_data_typed = my_var;
endmodule
module casting (
    input [7:0] i_int_8,
    input signed [7:0] i_signed_8,
    input real i_real_in,
    input string i_string_in,
    output signed [15:0] o_signed_cast,
    output unsigned [15:0] o_unsigned_cast,
    output [15:0] o_size_cast,
    output real o_real_cast,
    output logic [31:0] o_int_from_real_cast,
    output string o_string_cast,
    output int o_int_from_string_cast,
    output bit o_dynamic_cast
);
    typedef logic [15:0] t_size_cast;
    typedef enum {A, B} my_enum_t;
    my_enum_t my_enum_var;
    assign o_signed_cast = $signed(i_int_8);
    assign o_unsigned_cast = $unsigned(i_signed_8);
    assign o_size_cast = t_size_cast'(i_int_8);
    assign o_real_cast = real'(i_int_8);
    assign o_int_from_real_cast = int'(i_real_in);
    assign o_string_cast = string'(i_int_8);
    assign o_int_from_string_cast = int'(i_string_in);
    always_comb begin
        o_dynamic_cast = $cast(my_enum_var, i_int_8);
    end
endmodule
module system_funcs_math (
    input [31:0] i_data,
    input int i_array_dim_idx,
    input int i_rand_seed,
    output int o_bits,
    output int o_clog2,
    output int o_dimensions,
    output int o_left,
    output int o_right,
    output int o_low,
    output int o_high,
    output int o_size,
    output int o_increment,
    output int o_random,
    output int o_urandom,
    output int o_urandom_range,
    output int o_countbits_0,
    output int o_countbits_1,
    output int o_countbits_x,
    output int o_countbits_z,
    output int o_countones
);
    logic [7:0] my_array [0:3];
    assign o_bits = $bits(i_data);
    assign o_clog2 = $clog2(i_data);
    assign o_dimensions = $dimensions(my_array);
    assign o_left = $left(my_array, i_array_dim_idx);
    assign o_right = $right(my_array, i_array_dim_idx);
    assign o_low = $low(my_array, i_array_dim_idx);
    assign o_high = $high(my_array, i_array_dim_idx);
    assign o_size = $size(my_array, i_array_dim_idx);
    assign o_increment = $increment(my_array, i_array_dim_idx);
    always_comb begin
        o_random = $random(i_rand_seed);
        o_urandom = $urandom();
        o_urandom_range = $urandom_range(100, 10);
        o_countbits_0 = $countbits(0, i_data);
        o_countbits_1 = $countbits(1, i_data);
        o_countbits_x = $countbits(4'bX, i_data);
        o_countbits_z = $countbits(4'bZ, i_data);
    end
    assign o_countones = $countones(i_data);
endmodule
module system_funcs_time (
    input int i_time_units,
    input int i_time_precision,
    input string i_time_suffix,
    input int i_time_width,
    output real o_realtime,
    output int o_time_units_func,
    output int o_time_precision_func
);
    assign o_realtime = $realtime;
    assign o_time_units_func = $timeunit;
    assign o_time_precision_func = $timeprecision;
    always_comb begin
        $timeformat(i_time_units, i_time_precision, i_time_suffix, i_time_width);
    end
endmodule
module system_funcs_io (
    input string i_filename,
    input string i_mode,
    input int i_file_desc,
    input [7:0] i_data_to_write,
    input int i_read_start,
    input int i_read_count,
    input string i_plusargs_search,
    input int i_value_plusargs_default,
    input int i_fseek_offset,
    input int i_fseek_op,
    output int o_fopen_desc,
    output int o_ferror,
    output int o_feof,
    output int o_ftell,
    output int o_fgetc,
    output int o_fread,
    output int o_test_plusargs,
    output int o_value_plusargs,
    output int o_fseek_status
);
    string ferr_str;
    assign o_fopen_desc = $fopen(i_filename, i_mode);
    assign o_ferror = $ferror(i_file_desc, ferr_str);
    assign o_feof = $feof(i_file_desc);
    assign o_ftell = $ftell(i_file_desc);
    assign o_fgetc = $fgetc(i_file_desc);
    assign o_fread = $fread(i_data_to_write, i_file_desc, i_read_start, i_read_count);
    assign o_test_plusargs = $test$plusargs(i_plusargs_search);
    assign o_value_plusargs = $value$plusargs(i_plusargs_search, i_value_plusargs_default);
    assign o_fseek_status = $fseek(i_file_desc, i_fseek_offset, i_fseek_op);
    always_comb begin
        $fclose(i_file_desc);
        $fflush(i_file_desc);
    end
endmodule
module string_methods (
    input string i_string_in_1,
    input string i_string_in_2,
    input int i_char_index,
    input [7:0] i_char_value,
    input int i_substr_start,
    input int i_substr_len,
    input int i_int_in,
    input real i_real_in,
    output int o_len,
    output string o_tolower,
    output string o_toupper,
    output int o_compare,
    output int o_icompare,
    output [7:0] o_getc,
    output string o_substr,
    output int o_atoi,
    output real o_atoreal,
    output string o_itoa,
    output string o_hextoa,
    output string o_octtoa,
    output string o_bintoa,
    output string o_realtoa
);
    string string_var;
    string string_var_putc;
    always_comb begin
        string_var = i_string_in_1;
        string_var_putc = i_string_in_1;
        o_len = string_var.len();
        o_tolower = string_var.tolower();
        o_toupper = string_var.toupper();
        o_compare = string_var.compare(i_string_in_2);
        o_icompare = string_var.icompare(i_string_in_2);
        string_var_putc = string_var_putc.putc(i_char_index, i_char_value);
        o_getc = string_var.getc(i_char_index);
        o_substr = string_var.substr(i_substr_start, i_substr_len);
        o_atoi = string_var.atoi();
        o_atoreal = string_var.atoreal();
        o_itoa = string_var.itoa(i_int_in);
        o_hextoa = string_var.hextoa(i_int_in);
        o_octtoa = string_var.octtoa(i_int_in);
        o_bintoa = string_var.bintoa(i_int_in);
        o_realtoa = string_var.realtoa(i_real_in);
    end
endmodule
module array_queue_methods (
    input [7:0] i_element,
    input int i_index,
    input [7:0] i_dyn_array_in [],
    input [7:0] i_queue_in [$],
    output int o_dyn_size,
    output int o_queue_size,
    output [7:0] o_dyn_at,
    output [7:0] o_queue_at,
    output [7:0] o_queue_at_back,
    output [7:0] o_queue_pop_front,
    output [7:0] o_queue_pop_back,
    output int o_dyn_sum,
    output int o_queue_sum
);
    logic [7:0] dyn_array [];
    logic [7:0] queue [$];
    logic [7:0] queue_result_pop_front;
    logic [7:0] queue_result_pop_back;
    int dyn_sum_var;
    int queue_sum_var;
    always_comb begin
        dyn_array = i_dyn_array_in;
        queue = i_queue_in;
        o_dyn_size = dyn_array.size();
        o_queue_size = queue.size();
        o_dyn_at = dyn_array.at(i_index);
        o_queue_at = queue.at(i_index);
        o_queue_at_back = queue.at(queue.size() - 1);
        dyn_array.delete();
        queue.clear();
        queue.push_front(i_element);
        queue.push_back(i_element);
        queue.insert(i_index, i_element);
        queue_result_pop_front = queue.pop_front();
        queue_result_pop_back = queue.pop_back();
        o_queue_pop_front = queue_result_pop_front;
        o_queue_pop_back = queue_result_pop_back;
        dyn_sum_var = dyn_array.sum();
        queue_sum_var = queue.sum();
    end
    assign o_dyn_sum = dyn_sum_var;
    assign o_queue_sum = queue_sum_var;
endmodule
module procedural_blocks (
    input bit i_cond_if,
    input int i_case_expr,
    input [3:0] i_for_data [0:7],
    input int i_while_iter,
    input int i_repeat_count,
    input event i_wait_event,
    input bit i_wait_cond,
    input bit i_posedge_sig,
    output bit o_if_out,
    output bit o_case_out,
    output [3:0] o_for_sum,
    output int o_while_count,
    output [3:0] o_repeat_sum,
    output bit o_wait_out
);
    logic [3:0] for_sum_var;
    int while_count_var;
    int repeat_count_var;
    always_comb begin
        int j;
        if (i_cond_if) begin
            o_if_out = 1'b1;
        end else begin
            o_if_out = 1'b0;
        end
        case (i_case_expr)
            1: o_case_out = 1'b1;
            default: o_case_out = 1'b0;
        endcase
        for_sum_var = 4'b0;
        for (j=0; j<8; j++) begin
            for_sum_var = for_sum_var + i_for_data[j];
        end
        o_for_sum = for_sum_var;
        while_count_var = 0;
        while (while_count_var < i_while_iter) begin
            while_count_var++;
        end
        o_while_count = while_count_var;
        repeat_count_var = i_repeat_count;
        repeat (repeat_count_var) begin
        end
        o_repeat_sum = 4'b0;
        wait (i_wait_cond) ;
        o_wait_out = 1'b0;
        fork
           begin end
        join_none
        @(i_wait_event) ;
        @(posedge i_posedge_sig) ;
    end
endmodule
module assign_release (
    input [7:0] i_assign_value,
    input logic [7:0] i_force_value,
    output logic [7:0] o_assigned_var,
    output logic [7:0] o_forced_var
);
    logic [7:0] assigned_var;
    logic [7:0] forced_var;
    assign assigned_var = i_assign_value;
    always_comb begin
        assigned_var = i_assign_value + 1;
        force forced_var = i_force_value;
        release forced_var;
        o_assigned_var = assigned_var;
        o_forced_var = forced_var;
    end
endmodule
module assertion_property (
    input bit i_clk,
    input bit i_a,
    input bit i_b,
    output bit o_assert_triggered
);
    property p_a_implies_b;
        @(posedge i_clk) i_a |-> i_b;
    endproperty
    always_comb begin
        assert property(p_a_implies_b);
        cover property(p_a_implies_b);
        o_assert_triggered = 1'b0;
    end
endmodule
module assign_pattern_struct (
    input [7:0] i_field1,
    input [7:0] i_field2,
    input int i_member_b,
    input [7:0] i_member_a_default,
    output packed_struct_t o_packed_struct,
    output unpacked_struct_t o_unpacked_struct
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } packed_struct_t;
    typedef struct {
        logic [7:0] member_a;
        int member_b;
    } unpacked_struct_t;
    assign o_packed_struct = '{i_field1, i_field2};
    assign o_unpacked_struct = '{member_a: i_member_a_default, member_b: i_member_b};
    unpacked_struct_t unpacked_struct_default;
    assign unpacked_struct_default = '{default: i_member_b, member_a: i_member_a_default};
endmodule
module assign_pattern_array (
    input [7:0] i_elem0,
    input [7:0] i_elem1,
    input [7:0] i_default_elem,
    input [7:0] i_repl_elem,
    output logic [7:0] o_packed_array [0:1],
    output logic [7:0] o_unpacked_array [0:1],
    output logic [7:0] o_packed_array_default [0:1],
    output logic [7:0] o_packed_array_indexed [0:1],
    output logic [7:0] o_packed_array_repl [0:3]
);
    assign o_packed_array = '{i_elem0, i_elem1};
    assign o_unpacked_array = '{i_elem0, i_elem1};
    assign o_packed_array_default = '{0: i_elem0, default: i_default_elem};
    assign o_packed_array_indexed = '{1: i_elem1, 0: i_elem0};
    assign o_packed_array_repl = '{4{i_repl_elem}};
endmodule
module assign_pattern_assoc (
    input int i_key1,
    input int i_key2,
    input [7:0] i_val1,
    input [7:0] i_val2,
    input [7:0] i_default_val,
    output logic [7:0] o_assoc_array [int]
);
    assign o_assoc_array = '{i_key1: i_val1, i_key2: i_val2, default: i_default_val};
endmodule
module assign_pattern_queue (
    input [7:0] i_elem1,
    input [7:0] i_elem2,
    output logic [7:0] o_queue [$],
    output logic [7:0] o_empty_queue [$]
);
    logic [7:0] my_queue [$];
    always_comb begin
        my_queue = {}; 
        my_queue.push_back(i_elem1);
        my_queue.push_back(i_elem2);
        o_queue = my_queue;
        my_queue.clear(); 
        o_empty_queue = my_queue;
    end
endmodule
interface my_interface;
    logic [7:0] data;
    logic clk;
    modport master (output data, input clk);
    modport slave (input data, output clk);
end interface
module interface_modport (
    my_interface i_iface,
    output logic [7:0] o_data_from_iface
);
    assign o_data_from_iface = i_iface.data;
endmodule
module child_module (
    input [7:0] i_data,
    output [7:0] o_data_plus_1
);
    assign o_data_plus_1 = i_data + 1;
endmodule
module cell_instance (
    input [7:0] i_inst_data,
    output [7:0] o_inst_data_out,
    output [7:0] o_inst_array_out [0:1]
);
    child_module inst_single (.i_data(i_inst_data), .o_data_plus_1(o_inst_data_out));
    child_module inst_array [0:1] (.i_data(i_inst_data), .o_data_plus_1(o_inst_array_out));
endmodule
module randomization (
    input int i_seed,
    input bit i_rand_mode_on,
    input bit i_constraint_mode_on,
    output int o_rand_val
);
    class my_rand_class;
        rand int rand_var;
        constraint c1 { rand_var > 0; rand_var < 1000; }
        function new();
        endfunction
    endclass
    my_rand_class rand_inst;
    int status;
    always_comb begin
        rand_inst = new();
        status = rand_inst.randomize();
        status = rand_inst.srandom(i_seed);
        status = rand_inst.rand_mode(i_rand_mode_on);
        status = rand_inst.constraint_mode(i_constraint_mode_on);
        o_rand_val = rand_inst.rand_var;
    end
endmodule
module dynamic_array_new (
    input int i_size,
    output logic [7:0] o_dyn_array []
);
    logic [7:0] dyn_array [];
    always_comb begin
        dyn_array = new[i_size];
        o_dyn_array = dyn_array;
    end
endmodule
module dist_ops (
    input int i_seed,
    output int o_dist_uniform,
    output int o_dist_normal
);
    always_comb begin
        o_dist_uniform = $dist_uniform(i_seed, 10, 20);
        o_dist_normal = $dist_normal(i_seed, 50, 5);
    end
endmodule
module streaming_ops (
    input logic [15:0] i_packed_in,
    input logic [7:0] i_array_in [0:1],
    output logic [7:0] o_packed_out [0:1],
    output logic [15:0] o_array_out_packed
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } packed_struct_t;
    packed_struct_t packed_var;
    logic [7:0] array_var [0:1];
    assign packed_var = i_packed_in;
    assign array_var = i_array_in;
    assign o_packed_out = {>>{packed_var}};
    assign o_array_out_packed = {<<{array_var}};
endmodule
module unbounded_check (
    input logic [7:0] i_queue_in [$],
    input logic [7:0] i_dyn_array_in [],
    output bit o_is_unbounded_queue,
    output bit o_is_unbounded_dyn_array
);
    assign o_is_unbounded_queue = $is_unbounded(i_queue_in);
    assign o_is_unbounded_dyn_array = $is_unbounded(i_dyn_array_in);
endmodule
module system_task_func_calls (
    input int i_arg,
    output int o_func_out
);
    int func_result;
    always_comb begin
        $system("echo 'Hello from $system task'");
        func_result = $system("echo 'Hello from $system function'");
    end
    assign o_func_out = func_result;
endmodule
module sformatf_usage (
    input int i_int_val,
    input real i_real_val,
    output string o_formatted_string
);
    assign o_formatted_string = $sformatf("Integer: %0d, Real: %g", i_int_val, i_real_val);
endmodule
module assertion_control (
    input bit i_enable,
    output bit o_dummy
);
    always_comb begin
        if (i_enable) $asserton;
        else $assertoff;
    end
    assign o_dummy = i_enable;
endmodule
module gate_primitive (
    input i_a,
    input i_b,
    output o_and_out
);
    and g_and (o_and_out, i_a, i_b);
endmodule
module simple_function (
    input int i_func_in,
    output int o_func_out
);
    function automatic int add_one(input int val);
        return val + 1;
    endfunction
    assign o_func_out = add_one(i_func_in);
endmodule
module memory_read_write (
    input int i_read_addr,
    input int i_write_addr,
    input [7:0] i_write_data,
    input string i_filename,
    output [7:0] o_read_data
);
    logic [7:0] mem [0:7];
    always_comb begin
        $readmemh(i_filename, mem, i_read_addr, i_read_addr + 1);
        $writememh(i_filename, mem, i_write_addr, i_write_addr + 1);
        o_read_data = mem[i_read_addr];
    end
endmodule
module event_expr_funcs (
    input logic i_sig,
    input event i_event,
    input int i_delay_ticks,
    output bit o_fell,
    output bit o_rose,
    output logic o_sampled,
    output logic o_past
);
    always_comb begin
        o_fell = $fell(i_sig);
        o_rose = $rose(i_sig);
        o_sampled = $sampled(i_sig);
        o_past = $past(i_sig, i_delay_ticks, 1);
    end
endmodule

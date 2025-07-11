import "DPI-C" function int get_dpi_array_size(input int arr[]);
interface simple_if;
    logic clk;
    logic data;
    modport mp_in (input clk, data);
    modport mp_out (output clk, data);
endinterface
typedef class forward_my_class_t;
class forward_my_class_t;
    int data;
    function new(); data = 0; endfunction
endclass
typedef struct { int data; } my_struct_t;
typedef struct packed {
    logic [3:0] field_ps1;
} my_packed_struct_t;
typedef int my_queue_t[$];
typedef enum { ALIAS_A, ALIAS_B } my_enum_t;
typedef struct packed {
    logic [3:0] field1;
    logic [3:0] field2;
} packed_struct_t;
typedef struct packed {
    logic [3:0] field_ok;
} packed_struct_good_member_t;
typedef struct packed {
    logic [3:0] field_a;
    logic [3:0] field_b;
} packed_struct_no_init_t;
typedef struct {
    int field_int;
    real field_real;
    logic [7:0] field_vec;
    rand int rand_field;
    randc logic [3:0] randc_field;
} unpacked_struct_t;
typedef union packed {
    logic [7:0] u_field1;
    logic [7:0] u_field2;
} packed_union_t;
typedef union {
    int uv_field1;
    real uv_field2;
} unpacked_union_t;
typedef union {
    int uv_field_int;
    real uv_field_real;
} unpacked_union_real_t;
typedef union tagged {
    int tu_field_int;
    real tu_field_real;
} tagged_union_t;
typedef union {
    int good_member;
} unpacked_union_good_member_t;
typedef enum { E_A_alias, E_B_alias = 5, E_C_alias } simple_enum_t;
typedef enum bit [2:0] { E_D=0, E_E=1, E_F=7 } base_type_enum_t;
typedef enum { E_G [0:3] } range_enum_t;
typedef enum { D_H = 1, D_I = 2, D_J = 3 } duplicate_enum_t;
typedef enum bit [1:0] { O_J=0, O_K=1, O_L=3 } overflow_enum_t;
typedef enum bit [1:0] { O_M=0, O_N=2 } overflow_enum_check_t;
typedef enum logic { U_M = 0, U_X = 1 } unknown_bits_default_t;
typedef enum bit [0:0] { U_N = 0, U_Z = 1 } unknown_bits_2state_t;
class class_with_typedefs;
    local typedef int local_int_t;
    protected typedef real protected_real_t;
    typedef my_struct_t my_internal_struct_t;
    local_int_t local_var;
    protected_real_t protected_var;
    my_internal_struct_t struct_var_in_class;
    function new();
        local_var = 1;
        protected_var = 1.0;
        struct_var_in_class.data = 1;
    endfunction
endclass
module m_integral_scalar_packed (
    input byte byte_in,
    input int int_in,
    input shortint shortint_in,
    input longint longint_in,
    input integer integer_in,
    input time time_in,
    input bit bit_in,
    input logic logic_in,
    input reg reg_in,
    input logic [15:0] vec_in,
    input int signed_int_in,
    input logic unsigned [7:0] unsigned_logic_in,
    output byte byte_out,
    output int int_out,
    output shortint shortint_out,
    output longint longint_out,
    output integer integer_out,
    output time time_out,
    output bit bit_out,
    output logic logic_out,
    output reg reg_out,
    output logic [15:0] vec_out,
    output int signed_int_out,
    output logic unsigned [7:0] unsigned_logic_out
);
    byte byte_var;
    int int_var;
    shortint shortint_var;
    longint longint_var;
    integer integer_var;
    time time_var;
    bit bit_var;
    logic logic_var;
    reg reg_var;
    logic [7:0] packed_logic_vec;
    reg signed [3:0] packed_reg_signed_vec;
    bit unsigned [2:0] packed_bit_unsigned_vec;
    int signed_int_var;
    logic [7:0] unsigned_logic_var;
    always_comb begin
        byte_var = byte_in;
        int_var = int_in;
        shortint_var = shortint_in;
        longint_var = longint_in;
        integer_var = integer_in;
        time_var = time_in;
        bit_var = bit_in;
        logic_var = logic_in;
        reg_var = reg_in;
        packed_logic_vec = vec_in[7:0];
        packed_reg_signed_vec = {reg_in, bit_in, logic_in, packed_logic_vec[0]};
        packed_bit_unsigned_vec = {bit_in, logic_in, reg_in};
        signed_int_var = signed_int_in;
        unsigned_logic_var = unsigned_logic_in;
        byte_out = byte_var;
        int_out = int_var;
        shortint_out = shortint_var;
        longint_out = longint_var;
        integer_out = integer_var;
        time_out = time_var;
        bit_out = bit_var;
        logic_out = logic_var;
        reg_out = reg_var;
        vec_out = {packed_logic_vec, packed_logic_vec};
        signed_int_out = signed_int_var;
        unsigned_logic_out = unsigned_logic_var;
    end
endmodule
module m_float_string_enum (
    input real real_in,
    input shortreal shortreal_in,
    input realtime realtime_in,
    input string string_in,
    input int enum_base_in,
    output real real_out,
    output shortreal shortreal_out,
    output realtime realtime_out,
    output string string_out,
    output int simple_enum_out_val,
    output int base_enum_out_val
);
    real real_var;
    shortreal shortreal_var;
    realtime realtime_var;
    string string_var;
    simple_enum_t simple_enum_var;
    base_type_enum_t base_type_enum_var;
    range_enum_t range_enum_var [0:3];
    duplicate_enum_t duplicate_enum_var;
    overflow_enum_t overflow_enum_var;
    unknown_bits_default_t unknown_bits_default_var;
    unknown_bits_2state_t unknown_bits_2state_var;
    overflow_enum_check_t overflow_enum_check_var;
    always_comb begin
        real_var = real_in;
        shortreal_var = shortreal_in;
        realtime_var = realtime_in;
        string_var = string_in;
        if (string_var == "") begin
            string_var = "default_string";
        end
        simple_enum_var = simple_enum_t'(enum_base_in);
        base_type_enum_var = base_type_enum_t'(enum_base_in);
        range_enum_var[0] = range_enum_t'(enum_base_in % 4);
        range_enum_var[1] = range_enum_t'(1);
        range_enum_var[2] = range_enum_t'(2);
        range_enum_var[3] = range_enum_t'(3);
        duplicate_enum_var = duplicate_enum_t'(1);
        overflow_enum_var = overflow_enum_t'(enum_base_in % 4);
        unknown_bits_default_var = unknown_bits_default_t'(0);
        unknown_bits_2state_var = unknown_bits_2state_t'(0);
        overflow_enum_check_var = overflow_enum_check_t'(2);
        string_out = string_var;
        real_out = real_var;
        shortreal_out = shortreal_var;
realtime_out = realtime_var;
    simple_enum_out_val = int'(simple_enum_var);
    base_enum_out_val = int'(base_type_enum_var);
    end
endmodule
module m_struct_union (
    input logic [7:0] packed_in,
    input int unpacked_int_in,
    input real unpacked_real_in,
    output logic [7:0] packed_out,
    output int unpacked_int_out,
    output real unpacked_real_out,
    output int unpacked_union_int_out,
    output real tagged_union_real_out,
    output real unpacked_union_real_out_val,
    output int unpacked_union_good_out,
    output int dummy_unpacked_struct_read_out,
    output int dummy_unpacked_union_read_out,
    output logic [7:0] dummy_packed_union_read_out
);
    packed_struct_t packed_struct_var;
    unpacked_struct_t unpacked_struct_var;
    packed_union_t packed_union_var;
    unpacked_union_t unpacked_union_var;
    unpacked_union_real_t unpacked_union_real_var;
    tagged_union_t tagged_union_var;
    unpacked_union_good_member_t unpacked_union_good_var;
    always_comb begin
        automatic int dummy_unpacked_struct_read;
        automatic int dummy_unpacked_union_read;
        automatic logic [7:0] dummy_packed_union_read;
        dummy_unpacked_struct_read = unpacked_struct_var.field_int;
        dummy_unpacked_struct_read_out = dummy_unpacked_struct_read;
        dummy_unpacked_union_read = unpacked_union_var.uv_field1;
        dummy_unpacked_union_read_out = dummy_unpacked_union_read;
        dummy_packed_union_read = packed_union_var.u_field1;
        dummy_packed_union_read_out = dummy_packed_union_read;
        packed_struct_var.field1 = packed_in[7:4];
        packed_struct_var.field2 = packed_in[3:0];
        packed_out = {packed_struct_var.field1, packed_struct_var.field2};
        unpacked_struct_var.field_int = unpacked_int_in;
        unpacked_struct_var.field_real = unpacked_real_in;
        unpacked_struct_var.field_vec = packed_in;
        unpacked_int_out = unpacked_struct_var.field_int;
        unpacked_real_out = unpacked_struct_var.field_real;
        packed_union_var.u_field1 = packed_in;
        unpacked_union_var.uv_field1 = unpacked_int_in;
        unpacked_union_int_out = unpacked_union_var.uv_field1;
        unpacked_union_real_var.uv_field_real = unpacked_real_in;
        unpacked_union_real_out_val = unpacked_union_real_var.uv_field_real;
        unpacked_union_real_var.uv_field_int = unpacked_int_in;
        tagged_union_var.tu_field_real = unpacked_real_in;
        tagged_union_real_out = tagged_union_var.tu_field_real;
        unpacked_union_good_var.good_member = unpacked_int_in;
        unpacked_union_good_out = unpacked_union_good_var.good_member;
    end
endmodule
module m_unpacked_arrays_queues (
    input int fixed_array_in [0:3],
    input int queue_in [$],
    input int dyn_array_size,
    input string assoc_key_in,
    input real assoc_value_in,
    input bit [7:0] fixed_vec_array_in [2:0],
    output int fixed_array_out [0:3],
    output int queue_out [$],
    output real assoc_value_out,
    output int multi_dim_out,
    output int dyn_array_size_out,
    output int dyn_array_val_out,
    output real bounded_queue_val_out,
    output bit assoc_exists_out,
    output int assoc_first_key_out,
    output int dummy_fixed_array_read_out,
    output int dummy_dyn_array_read_size_out,
    output int dummy_assoc_size_out,
    output int dummy_queue_size_out,
    output int dummy_real_queue_size_out
);
    int fixed_size_array [0:3];
    logic [7:0] fixed_vec_array [2:0];
    int multi_dim_array [0:1][0:2];
    int dynamic_array [];
    bit dynamic_bit_array [];
    string associative_array [int];
    real associative_real_array [string];
    bit [3:0] associative_vec_array [int];
    int int_queue [$];
    logic [1:0] logic_queue [$];
    real real_queue [$:10];
    always_comb begin
        automatic real temp_val;
        automatic string first_string_key;
        automatic int first_int_key;
        automatic int delete_key = 0;
        automatic int dummy_fixed_array_read;
        automatic int dummy_dyn_array_read_size;
        automatic int dummy_assoc_size;
        automatic int dummy_queue_size;
        automatic int dummy_real_queue_size;
        automatic int i;
        dummy_fixed_array_read = fixed_size_array[0];
        dummy_fixed_array_read_out = dummy_fixed_array_read;
        dummy_dyn_array_read_size = dynamic_array.size();
        dummy_dyn_array_read_size_out = dummy_dyn_array_read_size;
        dummy_assoc_size = associative_array.size();
        dummy_assoc_size_out = dummy_assoc_size;
        dummy_queue_size = int_queue.size();
        dummy_queue_size_out = dummy_queue_size;
        dummy_real_queue_size = real_queue.size();
        dummy_real_queue_size_out = dummy_real_queue_size;
        fixed_size_array = fixed_array_in;
        fixed_array_out = fixed_size_array;
        for (i = 0; i < 3; i++) begin
            fixed_vec_array[i] = fixed_vec_array_in[i];
        end
        int_queue = queue_in;
        queue_out = int_queue;
        if (real_queue.size() < 10) begin
            real_queue.push_back(assoc_value_in);
        end
        if (real_queue.size() > 0) begin
            bounded_queue_val_out = real_queue[0];
        end else begin
            bounded_queue_val_out = 0.0;
        end
        if (dyn_array_size >= 0 && dyn_array_size < 10) begin
            dynamic_array = new[dyn_array_size];
            dyn_array_size_out = dynamic_array.size();
            if (dynamic_array.size() > 0) begin
                dynamic_array[0] = dyn_array_size;
                dyn_array_val_out = dynamic_array[0];
            end else begin
                dyn_array_val_out = 0;
            end
            dynamic_array.delete();
        end else begin
            dynamic_array = new[0];
            dyn_array_size_out = 0;
            dyn_array_val_out = 0;
        end
        associative_real_array[assoc_key_in] = assoc_value_in;
        if (associative_real_array.exists(assoc_key_in)) begin
            temp_val = associative_real_array[assoc_key_in];
            assoc_value_out = temp_val;
            assoc_exists_out = 1;
            associative_real_array.delete(assoc_key_in);
        end else begin
            assoc_value_out = 0.0;
            assoc_exists_out = 0;
        end
        associative_vec_array[delete_key] = 4'b1010;
        associative_vec_array.delete(delete_key);
        if (associative_vec_array.first(first_int_key)) begin
            assoc_first_key_out = first_int_key;
        end else begin
            assoc_first_key_out = -1;
        end
        multi_dim_array[0][0] = fixed_array_in[0];
        multi_dim_array[1][2] = fixed_array_in[3];
        multi_dim_out = multi_dim_array[0][0] + multi_dim_array[1][2];
    end
endmodule
module m_handles_virtual_if_dpi (
    input event event_in,
    input logic [63:0] chandle_in_data,
    input string string_in,
    input int dummy_dpi_input,
    output event event_out,
    output logic [63:0] chandle_out_data,
    output logic if_data_out,
    output string string_out,
    output int dpi_array_size_out
);
    event event_var;
    event another_event;
    chandle chandle_var = null;
    chandle null_chandle = null;
    string string_var = "";
    virtual simple_if virtual_if_var = null;
    virtual simple_if.mp_in virtual_if_mp_in_var = null;
    virtual simple_if.mp_out virtual_if_mp_out_var = null;
    int dummy_dpi_array[5];
    always_comb begin
        chandle_var = null;
        chandle_out_data = 0;
        string_var = string_in;
        if (string_var == "") begin
            string_var = "empty_string";
        end else begin
        end
        string_out = string_var;
        if (virtual_if_var != null) begin
            if_data_out = 1;
        end else begin
            if_data_out = 0;
        end
        dummy_dpi_array[0] = dummy_dpi_input;
        dummy_dpi_array[4] = dummy_dpi_input + 1;
        dpi_array_size_out = get_dpi_array_size(dummy_dpi_array);
        event_out = event_var;
    end
endmodule
module m_class_and_typedefs (
    input logic trigger_in,
    output int class_var_data_out,
    output int local_var_out,
    output real protected_var_out,
    output int forward_class_data_out
);
    class_with_typedefs my_class_h = null;
    forward_my_class_t my_forward_class_h = null;
    always_comb begin
        if (trigger_in) begin
            my_class_h = new();
            my_forward_class_h = new();
            class_var_data_out = my_class_h.struct_var_in_class.data;
            local_var_out = my_class_h.local_var;
            protected_var_out = my_class_h.protected_var;
            my_forward_class_h.data = 10;
            forward_class_data_out = my_forward_class_h.data;
        end else begin
            my_class_h = null;
            my_forward_class_h = null;
            class_var_data_out = 0;
            local_var_out = 0;
            protected_var_out = 0.0;
            forward_class_data_out = 0;
        end
    end
endmodule

class base_class;
    int b_field;
    function new(int val);
        b_field = val;
    endfunction
    virtual function void dummy_method();
    endfunction
endclass
class derived_class extends base_class;
    string d_field;
    function new(int val, string s);
        super.new(val);
        d_field = s;
    endfunction
    virtual function void dummy_method();
    endfunction
endclass
interface class my_interface_class;
    pure virtual function void interface_method();
endclass
class implementing_class extends base_class implements my_interface_class;
    function new(int val);
        super.new(val);
    endfunction
    virtual function void dummy_method();
    endfunction
    virtual function void interface_method();
    endfunction
endclass
interface simple_if(input bit clk);
    logic sig;
endinterface
interface simple_if_for_valid(input bit clk);
    logic sig;
endinterface
class dpi_class_t;
    int val;
endclass
class my_class_for_valid;
    int val;
endclass
typedef struct { int val; } unpacked_struct_dpi_t;
typedef logic [7:0] fixed_unpacked_array_dpi_t [3:0];
typedef union { int a; byte b; } untagged_union_valid;
typedef union { int a; int fixed_array_mem[2]; } untagged_union_invalid_dyn_t;
typedef union tagged { int a; byte b; } tagged_union_valid;
typedef struct packed { logic [15:0] field1; logic [15:0] field2; } packed_struct_32_t;
typedef struct packed { logic [7:0] field1; logic [7:0] field2; } packed_struct_16_t;
typedef struct packed { logic [3:0] field1; logic [4:0] field2; } packed_struct_t;
typedef struct { int val1; real val2; } unpacked_struct_t;
typedef union packed { logic [7:0] data; byte num; } packed_union_t;
typedef union tagged { logic [7:0] data_tagged; byte num_tagged; } tagged_union_t;
typedef union { string name; real value; byte byte_val; } unpacked_union_t;
typedef union { int int_mem; byte byte_mem; } unpacked_union_simple_t;
typedef int my_integer_t;
typedef my_integer_t another_integer_alias;
typedef logic [7:0] UnpackedArrayForValid [3:0];
typedef struct { int a; byte b; } UnpackedStructForValid;
module BasicTypesOps (
    input  bit          clk,
    input  logic [7:0]  in_byte_unsigned,
    input  int          in_int,
    input  shortreal    in_sreal,
    input  string       in_string,
    output logic [15:0] out_logic_wide_unsigned,
    output integer      out_integer,
    output real         out_real,
    output string       out_string,
    output byte signed  out_byte_signed,
    output longint      out_longint,
    output bit          out_signed_check,
    output bit          out_fourstate_check
);
    always_comb begin
        logic [15:0] logic_var;
        integer int_var;
        real real_var;
        string string_var;
        byte signed byte_s_var;
        shortreal sreal_var;
        longint longint_var;
        logic [7:0] temp_logic;
        int temp_int;
        real temp_real;
        string temp_string;
        logic signed [7:0] byte_signed_logic;
        logic [7:0] byte_unsigned_logic;
        logic four_state_var;
        logic_var = in_byte_unsigned;
        int_var   = in_byte_unsigned;
        real_var  = in_sreal;
        string_var = in_string;
        byte_s_var = $signed(in_byte_unsigned);
        logic_var = $unsigned(in_int);
        int_var = int'(in_sreal);
        real_var = real'(in_int);
        string_var = string'(in_int);
        if (!in_string.len())
            int_var = 0;
        else
            int_var = int'(in_string);
        sreal_var = shortreal'(real_var);
        longint_var = longint'(int_var);
        out_logic_wide_unsigned = logic_var;
        out_integer = int_var;
        out_real = real_var;
        out_string = string_var;
        out_byte_signed = byte_s_var;
        out_longint = longint_var;
        temp_logic = in_int;
        temp_int   = in_sreal;
        temp_real  = in_byte_unsigned;
        temp_string = string'(in_int);
        out_logic_wide_unsigned = out_logic_wide_unsigned ^ temp_logic;
        out_integer = out_integer + temp_int;
        four_state_var = 1'bx;
        out_signed_check = $signed(in_byte_unsigned) < 0;
        out_fourstate_check = (four_state_var == 1'bx);
        byte_signed_logic = 8'sb11111111;
        byte_unsigned_logic = $unsigned(byte_signed_logic);
    end
endmodule
module ArrayAndStreamingOps (
    input  logic [3:0]  in_arr_packed,
    input  int          in_val_int,
    input  int          in_key_int,
    input  byte         in_byte_queue_val,
    input  logic [31:0] in_bits_stream,
    output logic [3:0]  out_arr_packed,
    output int          out_arr_unpacked_val,
    output int          out_arr_dynamic_size,
    output int          out_arr_assoc_val,
    output byte         out_arr_queue_val,
    output bit          out_byte_array_check,
    output bit          out_iterable_check,
    output logic [31:0] out_bits_stream_a,
    output logic [31:0] out_bits_stream_b,
    output logic [15:0] out_bits_stream_c
);
    logic [3:0] arr_packed;
    int arr_unpacked [7:0];
    int arr_dynamic [];
    int assoc_arr [int];
    byte queue_arr [$];
    byte byte_array [1:0];
    logic [7:0] eight_bit_chunks [0:3];
    packed_struct_32_t fixed_struct_32;
    packed_struct_16_t fixed_struct_16;
    always_comb begin
        logic [15:0] sixteen_bit_val;
        arr_packed = in_arr_packed;
        out_arr_packed = arr_packed;
        arr_unpacked[0] = in_val_int;
        out_arr_unpacked_val = arr_unpacked[0];
        arr_dynamic = new[in_val_int % 10 + 1];
        out_arr_dynamic_size = arr_dynamic.size();
        assoc_arr[in_key_int] = in_val_int;
        if (assoc_arr.exists(in_key_int))
            out_arr_assoc_val = assoc_arr[in_key_int];
        else
            out_arr_assoc_val = 0;
        queue_arr.push_back(in_byte_queue_val);
        if (queue_arr.size() > 0)
            out_arr_queue_val = queue_arr.pop_front();
        else
            out_arr_queue_val = 0;
        byte_array[0] = 8'hAA;
        byte_array[1] = 8'hBB;
        out_byte_array_check = (byte_array[0] == 8'hAA);
        eight_bit_chunks = {>>8{in_bits_stream}};
        out_bits_stream_a = {<<8{eight_bit_chunks}};
        fixed_struct_32 = {>>{in_bits_stream}};
        out_bits_stream_b = {<<{fixed_struct_32}};
        sixteen_bit_val = in_bits_stream[15:0];
        fixed_struct_16 = {>>{sixteen_bit_val}};
        out_bits_stream_c = {<<{fixed_struct_16}};
        out_iterable_check = 1'b1;
    end
endmodule
module StructAndUnionOps (
    input  logic [7:0] in_data_su,
    output int         out_val_struct_unpacked,
    output logic [7:0] out_val_union_packed_data,
    output byte        out_val_union_packed_num,
    output logic [7:0] out_val_union_tagged_data,
    output byte        out_val_union_tagged_num,
    output real        out_val_union_unpacked_real,
    output bit         out_union_unpacked_byte_check,
    output bit         out_is_struct_check,
    output bit         out_is_union_check,
    output bit         out_is_tagged_union_check
);
    packed_struct_t           ps_var;
    unpacked_struct_t         us_var;
    packed_union_t            pu_var;
    tagged_union_t            put_var;
    unpacked_union_t          uu_var;
    unpacked_union_simple_t   u_simple_var;
    always_comb begin
        ps_var.field1 = in_data_su[3:0];
        ps_var.field2 = in_data_su[7:3];
        us_var.val1   = $unsigned(in_data_su);
        us_var.val2   = 1.23;
        out_val_struct_unpacked = us_var.val1;
        pu_var.data = in_data_su;
        out_val_union_packed_data = pu_var.data;
        out_val_union_packed_num  = pu_var.num;
        put_var.data_tagged = in_data_su;
        out_val_union_tagged_data = put_var.data_tagged;
        put_var.num_tagged = byte'(in_data_su);
        out_val_union_tagged_num = put_var.num_tagged;
        uu_var.value = 3.14159;
        out_val_union_unpacked_real = uu_var.value;
        uu_var.byte_val = in_data_su;
        out_union_unpacked_byte_check = (uu_var.byte_val == in_data_su);
        out_is_struct_check = (us_var.val1 == us_var.val1);
        out_is_union_check = (uu_var.byte_val == uu_var.byte_val);
        out_is_tagged_union_check = (put_var.data_tagged == put_var.data_tagged);
        u_simple_var.int_mem  = $unsigned(in_data_su);
        u_simple_var.byte_mem = in_data_su;
    end
endmodule
module OOPSimulationAndHandles (
    input  bit          clk,
    input  int          in_int_oop,
    input  logic [7:0]  in_byte_for_string_like,
    output int          out_base_field,
    output bit          out_handle_check_null,
    output bit          out_handle_check_valid,
    output int          out_derived_field_len,
    output bit          out_is_class_check,
    output bit          out_is_virtual_interface_check,
    output bit          out_is_handle_check,
    output bit          out_is_derived_from_check,
    output bit          out_implements_check,
    output bit          out_can_be_string_like_int,
    output bit          out_can_be_string_like_byte_array,
    output bit          out_can_be_string_like_string
);
    base_class            base_var;
    derived_class         derived_var;
    my_interface_class    iface_var;
    implementing_class    impl_var;
    chandle               ch_var;
    event                 ev_var;
    virtual interface simple_if local_vif_var;
    always_comb begin
        logic [7:0] int_like_val;
        string str_val;
        byte byte_arr [1:0];
        base_var = new(in_int_oop);
        derived_var = new(in_int_oop, "hello_world");
        impl_var = new(in_int_oop);
        base_var = derived_var;
        iface_var = impl_var;
        base_var = null;
        iface_var = null;
        ch_var = null;
        local_vif_var = null;
        ev_var = ev_var;
        out_handle_check_null = (base_var == null) && (ch_var == null) && (local_vif_var == null);
        base_var = new(in_int_oop + 1);
        derived_var = new(in_int_oop + 2, "another_string");
        impl_var = new(in_int_oop + 3);
        out_base_field = derived_var.b_field;
        out_derived_field_len = derived_var.d_field.len();
        out_handle_check_valid = (derived_var != null) && (ch_var == null);
        out_is_class_check = (base_var != null);
        out_is_virtual_interface_check = (local_vif_var != null);
        out_is_handle_check = (ch_var == null);
        out_is_derived_from_check = (derived_var != null);
        out_implements_check = (iface_var != null);
        int_like_val = in_byte_for_string_like;
        str_val = "abc";
        byte_arr[0] = 8'h01;
        byte_arr[1] = 8'h02;
        out_can_be_string_like_int = (string'(int_like_val) != "");
        out_can_be_string_like_byte_array = (byte_arr[0] == 8'h01);
        out_can_be_string_like_string = (str_val == "abc");
    end
endmodule
module AdvancedFeaturesAndValidation (
    input  logic [7:0] in_val_adv,
    input  int         in_int_adv,
    input  bit         in_bit_adv,
    input  real        in_real_adv,
    input  string      in_string_adv,
    input  bit         clk,
    output int         out_typedeffed_val,
    output int         out_rand_int_val,
    output bit         out_rand_bit_val,
    output int         out_enum_val,
    output int         out_dpi_int_ret,
    output real        out_dpi_real_ret,
    output bit         out_dpi_bit_ret,
    output byte        out_dpi_array_ret,
    output bit         out_is_boolean_convertible_int,
    output bit         out_is_simple_bit_vector_logic,
    output bit         out_has_fixed_range_int,
    output int         out_get_fixed_range_left,
    output bit         out_get_integral_flags_signed,
    output bit         out_get_default_int_zero,
    output int         out_make_unsigned_val,
    output int         out_is_sequence_valid_int,
    output int         out_associative_index_type_check,
    output logic [31:0] out_streamed_struct_field1,
    output logic [31:0] out_streamed_struct_field2,
    output bit         out_is_fixed_size_int,
    output bit         out_is_array_check,
    output bit         out_is_unpacked_array_check,
    output bit         out_is_dynamically_sized_array_check,
    output bit         out_is_byte_array_check,
    output bit         out_is_handle_type_check,
    output bit         out_is_simple_type_check,
    output bit         out_is_aggregate_check,
    output bit         out_is_bitstream_type_int,
    output bit         out_is_bitstream_type_string,
    output bit         out_is_bitstream_type_unpacked_array,
    output bit         out_is_bitstream_type_unpacked_struct,
    output bit         out_is_derived_from_null,
    output bit         out_implements_null,
    output int         out_common_base_null
);
    parameter int PARAM_VAL = 10;
    localparam int LOCALPARAM_VAL = 20;
    const int CONST_VAL = 30;
    typedef enum logic [7:0] { RED = 8'hAA, GREEN = 8'h55, BLUE = 8'hFF } color_t;
    import "DPI-C" function int   c_add_one(int arg);
    import "DPI-C" function void  c_process_string(string s);
    import "DPI-C" function real  c_get_real();
    import "DPI-C" function chandle c_get_handle();
    import "DPI-C" function byte  c_process_array(int arr[]);
    import "DPI-C" function bit   c_get_bit();
    import "DPI-C" function void  c_process_struct(unpacked_struct_dpi_t arg);
    import "DPI-C" function void  c_process_fixed_array(fixed_unpacked_array_dpi_t arg);
    int sequence_int;
    string sequence_string;
    real sequence_real;
    logic [7:0] sequence_logic_array [3:0];
    struct  { int a; byte b; } sequence_struct;
    int assoc_arr_idx [string];
    my_integer_t typedeffed_int;
    another_integer_alias aliased_int;
    color_t color_var;
    int dpi_ret_val_local;
    real dpi_real_ret_local;
    chandle dpi_handle_ret_local;
    bit dpi_bit_ret_local;
    unpacked_struct_dpi_t dpi_struct_var;
    fixed_unpacked_array_dpi_t dpi_fixed_array_var;
    int dpi_array_var [];
    string key_s;
    logic [31:0] stream_source;
    packed_struct_32_t streamed_struct;
    int null_var = 0;
    base_class base_cls;
    logic [7:0] byte_array_var [];
    chandle chandle_var;
    always_comb begin
        int temp_param_const;
        logic signed [7:0] signed_logic;
        logic [7:0] unsigned_val;
        typedeffed_int = $unsigned(in_val_adv);
        aliased_int = typedeffed_int;
        out_typedeffed_val = aliased_int;
        temp_param_const = PARAM_VAL + LOCALPARAM_VAL + CONST_VAL;
        out_rand_int_val = in_int_adv;
        out_rand_bit_val = in_bit_adv;
        color_var = color_t'(in_val_adv);
        out_enum_val = int'(color_var);
        dpi_ret_val_local = c_add_one(in_int_adv);
        out_dpi_int_ret = dpi_ret_val_local;
        c_process_string(in_string_adv);
        dpi_real_ret_local = c_get_real();
        out_dpi_real_ret = dpi_real_ret_local;
        dpi_handle_ret_local = c_get_handle();
        dpi_bit_ret_local = c_get_bit();
        out_dpi_bit_ret = dpi_bit_ret_local;
        dpi_array_var = new[1];
        dpi_array_var[0] = in_int_adv;
        out_dpi_array_ret = c_process_array(dpi_array_var);
        dpi_struct_var.val = in_int_adv;
        c_process_struct(dpi_struct_var);
        dpi_fixed_array_var[0] = in_val_adv;
        c_process_fixed_array(dpi_fixed_array_var);
        out_is_boolean_convertible_int = (in_int_adv != 0);
        out_is_simple_bit_vector_logic = (in_val_adv == 8'b0);
        out_has_fixed_range_int = (in_int_adv == 0);
        out_get_fixed_range_left = in_val_adv[7];
        signed_logic = 8'sb10000000;
        out_get_integral_flags_signed = ($signed(signed_logic) < 0);
        out_get_default_int_zero = (int'(0) == 0);
        unsigned_val = in_val_adv;
        out_make_unsigned_val = $unsigned($signed(unsigned_val));
        sequence_int = in_int_adv;
        sequence_string = in_string_adv;
        sequence_real = in_real_adv;
        sequence_logic_array = '{default:in_val_adv[0]};
        sequence_struct.a = in_int_adv; sequence_struct.b = in_val_adv[0];
        out_is_sequence_valid_int = sequence_int;
        key_s = "my_key";
        assoc_arr_idx[key_s] = in_int_adv;
        out_associative_index_type_check = assoc_arr_idx.exists(key_s) ? assoc_arr_idx[key_s] : 0;
        stream_source = {in_val_adv, in_val_adv, in_val_adv, in_val_adv};
        streamed_struct = {>>{stream_source}};
        out_streamed_struct_field1 = streamed_struct.field1;
        out_streamed_struct_field2 = streamed_struct.field2;
        out_is_fixed_size_int = (in_int_adv == 0);
        out_is_array_check = (dpi_array_var.size() > 0);
        out_is_unpacked_array_check = (dpi_array_var.size() > 0);
        out_is_dynamically_sized_array_check = (dpi_array_var.size() > 0);
        byte_array_var = new[2];
        byte_array_var[0] = 8'hAA;
        byte_array_var[1] = 8'hBB;
        out_is_byte_array_check = (byte_array_var.size() > 0);
        out_is_handle_type_check = (chandle_var == null);
        out_is_simple_type_check = (in_int_adv == 0);
        out_is_aggregate_check = (byte_array_var.size() > 0);
        out_is_bitstream_type_int = (in_int_adv == 0);
        out_is_bitstream_type_string = (in_string_adv != "");
        out_is_bitstream_type_unpacked_array = ($size(dpi_fixed_array_var) > 0);
        out_is_bitstream_type_unpacked_struct = (dpi_struct_var.val == 0);
        base_cls = new(in_int_adv);
        out_is_derived_from_null = (null_var == 0);
        out_implements_null = (null_var == 0);
        out_common_base_null = null_var;
    end
endmodule
module TypeValidationChecks (
    input  bit                          clk,
    input  logic [7:0]                  in_byte,
    input  UnpackedArrayForValid        port_unpacked_array,
    input  UnpackedStructForValid       port_unpacked_struct,
    output logic [7:0]                  out_byte,
    output int                          out_array_val,
    output int                          out_struct_val,
    output bit                          out_union_valid_check,
    output bit                          out_port_valid_check_struct,
    output bit                          out_port_valid_check_array
);
    UnpackedStructForValid  struct_var_rand;
    UnpackedArrayForValid   array_var_rand;
    untagged_union_valid    u1;
    tagged_union_valid      u_tagged1;
    unpacked_struct_dpi_t   dpi_struct_var;
    fixed_unpacked_array_dpi_t dpi_fixed_array_var;
    always_comb begin
        out_byte = in_byte;
        out_array_val  = port_unpacked_array[0];
        out_struct_val = port_unpacked_struct.a;
        struct_var_rand.a = $unsigned(in_byte);
        struct_var_rand.b = in_byte;
        array_var_rand[0] = in_byte;
        u1.a = $unsigned(in_byte);
        u_tagged1.a = $unsigned(in_byte);
        out_union_valid_check = (u1.a == u_tagged1.a);
        dpi_struct_var.val = $unsigned(in_byte);
        dpi_fixed_array_var[0] = in_byte;
        out_port_valid_check_struct = (port_unpacked_struct.a != 0);
        out_port_valid_check_array  = ($size(port_unpacked_array) > 0);
    end
endmodule

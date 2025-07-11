module IntegerFormatModule #(
    parameter int DataWidth = 32
)(
    input logic [DataWidth-1:0] in_data,
    input bit in_signed,
    output logic [31:0] out_dummy
);
    localparam string format_d = "%d";
    localparam string format_h = "%h";
    localparam string format_b = "%b";
    localparam string format_o = "%o";
    localparam string format_width_d = "%10d";
    localparam string format_zero_pad_h = "%010h";
    localparam string format_left_justify_d = "%-10d";
    localparam string format_mixed = "Int: %d, Hex: %h, Bin: %b";
    localparam [DataWidth-1:0] data_pos = 32'd12345;
    localparam [DataWidth-1:0] data_neg = -32'sd12345;
    localparam [DataWidth-1:0] data_large = 32'hFEDCBA98;
    string formatted_d;
    string formatted_h;
    string formatted_b;
    string formatted_o;
    string formatted_width_d;
    string formatted_zero_pad_h;
    string formatted_left_justify_d;
    string formatted_mixed;
    always_comb begin
        formatted_d = "";
        formatted_h = "";
        formatted_b = "";
        formatted_o = "";
        formatted_width_d = "";
        formatted_zero_pad_h = "";
        formatted_left_justify_d = "";
        formatted_mixed = "";
        if (in_signed) begin
            formatted_d = $sformatf(format_d, data_neg);
            formatted_h = $sformatf(format_h, data_neg);
            formatted_b = $sformatf(format_b, data_neg);
            formatted_o = $sformatf(format_o, data_neg);
            formatted_width_d = $sformatf(format_width_d, data_neg);
            formatted_zero_pad_h = $sformatf(format_zero_pad_h, data_large);
            formatted_left_justify_d = $sformatf(format_left_justify_d, data_neg);
            formatted_mixed = $sformatf(format_mixed, data_neg, data_large, data_pos);
        end else begin
            formatted_d = $sformatf(format_d, data_pos);
            formatted_h = $sformatf(format_h, data_pos);
            formatted_b = $sformatf(format_b, data_pos);
            formatted_o = $sformatf(format_o, data_pos);
            formatted_width_d = $sformatf(format_width_d, data_pos);
            formatted_zero_pad_h = $sformatf(format_zero_pad_h, data_pos);
            formatted_left_justify_d = $sformatf(format_left_justify_d, data_pos);
            formatted_mixed = $sformatf(format_mixed, data_pos, data_large, data_neg);
        end
        out_dummy = DataWidth;
    end
endmodule

module FloatFormatModule (
    input real in_real,
    output logic [31:0] out_dummy
);
    localparam real data_real_pos = 123.456;
    localparam real data_real_neg = -7.89e-2;
    localparam real data_real_large = 1.23456789012345e+10;
    localparam string format_f = "%f";
    localparam string format_e = "%e";
    localparam string format_g = "%g";
    localparam string format_f_precision = "%.2f";
    localparam string format_e_width_precision = "%12.4e";
    localparam string format_g_left_justify = "%-15g";
    string formatted_f;
    string formatted_e;
    string formatted_g;
    string formatted_f_precision;
    string formatted_e_width_precision;
    string formatted_g_left_justify;
    always_comb begin
        formatted_f = "";
        formatted_e = "";
        formatted_g = "";
        formatted_f_precision = "";
        formatted_e_width_precision = "";
        formatted_g_left_justify = "";
        if (in_real > 0) begin
            formatted_f = $sformatf(format_f, data_real_pos);
            formatted_e = $sformatf(format_e, data_real_pos);
            formatted_g = $sformatf(format_g, data_real_pos);
            formatted_f_precision = $sformatf(format_f_precision, data_real_pos);
            formatted_e_width_precision = $sformatf(format_e_width_precision, data_real_pos);
            formatted_g_left_justify = $sformatf(format_g_left_justify, data_real_pos);
        end else begin
            formatted_f = $sformatf(format_f, data_real_neg);
            formatted_e = $sformatf(format_e, data_real_neg);
            formatted_g = $sformatf(format_g, data_real_neg);
            formatted_f_precision = $sformatf(format_f_precision, data_real_large);
            formatted_e_width_precision = $sformatf(format_e_width_precision, data_real_large);
            formatted_g_left_justify = $sformatf(format_g_left_justify, data_real_large);
        end
        out_dummy = $realtobits(in_real);
    end
endmodule

module StringCharTimeFormatModule (
    input string in_string,
    input byte in_char,
    input int in_time,
    output logic [31:0] out_dummy
);
    localparam string data_string = "Hello, World!";
    localparam byte data_char = byte'(65);
    localparam int data_time = 123456789;
    localparam string format_s = "%s";
    localparam string format_c = "%c";
    localparam string format_t = "%t";
    localparam string format_s_width = "%20s";
    localparam string format_t_width = "%25t";
    string formatted_s;
    string formatted_c;
    string formatted_t;
    string formatted_s_width;
    string formatted_t_width;
    always_comb begin
        formatted_s = "";
        formatted_c = "";
        formatted_t = "";
        formatted_s_width = "";
        formatted_t_width = "";
        if (in_string == "test") begin
            formatted_s = $sformatf(format_s, in_string);
            formatted_c = $sformatf(format_c, in_char);
            formatted_t = $sformatf(format_t, in_time);
            formatted_s_width = $sformatf(format_s_width, in_string);
            formatted_t_width = $sformatf(format_t_width, in_time);
        end else begin
            formatted_s = $sformatf(format_s, data_string);
            formatted_c = $sformatf(format_c, data_char);
            formatted_t = $sformatf(format_t, data_time);
            formatted_s_width = $sformatf(format_s_width, data_string);
            formatted_t_width = $sformatf(format_t_width, data_time);
        end
        out_dummy = in_char;
    end
endmodule

module RawStrengthFormatModule (
    input logic [63:0] in_raw_64,
    input logic [31:0] in_raw_32,
    input logic [3:0] in_strength_val,
    output logic [31:0] out_dummy
);
    localparam logic [63:0] data_raw_64 = 64'h1234567890ABCDEF;
    localparam logic [31:0] data_raw_32 = 32'hAABBCCDD;
    localparam logic [7:0] data_raw_mixed = 8'b10z1x0z1;
    localparam logic [3:0] data_strength = 4'b10xZ;
    localparam string format_u = "%u";
    localparam string format_z = "%z";
    localparam string format_v = "%v";
    string formatted_u_64;
    string formatted_u_32;
    string formatted_z_mixed;
    string formatted_v;
    always_comb begin
        formatted_u_64 = "";
        formatted_u_32 = "";
        formatted_z_mixed = "";
        formatted_v = "";
        if (in_raw_64[0]) begin
            formatted_u_64 = $sformatf(format_u, in_raw_64);
            formatted_u_32 = $sformatf(format_u, in_raw_32);
            formatted_z_mixed = $sformatf(format_z, data_raw_mixed);
            formatted_v = $sformatf(format_v, in_strength_val);
        end else begin
            formatted_u_64 = $sformatf(format_u, data_raw_64);
            formatted_u_32 = $sformatf(format_u, data_raw_32);
            formatted_z_mixed = $sformatf(format_z, data_raw_mixed);
            formatted_v = $sformatf(format_v, data_strength);
        end
        out_dummy = in_raw_32;
    end
endmodule

module PatternFormatModule (
    input logic [7:0] in_byte,
    output logic [31:0] out_dummy
);
    typedef struct packed {
        logic a;
        logic [2:0] b;
        int c;
    } packed_struct_t;
    typedef struct {
        byte d;
        real e;
    } unpacked_struct_t;
    typedef int fixed_array_t[3];
    typedef byte byte_q_t[$];
    typedef int int_assoc_t[string];
    localparam packed_struct_t const_packed_struct = '{a: 1'b1, b: 3'b101, c: 10};
    localparam unpacked_struct_t const_unpacked_struct = '{d: 'hFF, e: 3.14};
    localparam fixed_array_t const_fixed_array = '{1, 5, 9};
    localparam byte const_byte_val = 'hAB;
    localparam integer const_int_val = 42;
    localparam byte_q_t const_queue = {1, 2, 3};
    localparam int_assoc_t const_assoc = '{"key1": 100, "key2": 200};
    localparam string format_p = "%p";
    localparam string format_p_abbreviated = "%0p";
    string formatted_p_packed_struct;
    string formatted_p_unpacked_struct;
    string formatted_p_fixed_array;
    string formatted_p_byte;
    string formatted_p_int;
    string formatted_p_queue;
    string formatted_p_assoc;
    string formatted_p_abbreviated_packed_struct;
    string formatted_p_abbreviated_unpacked_struct;
    string formatted_p_abbreviated_fixed_array;
    string formatted_p_abbreviated_queue;
    string formatted_p_abbreviated_assoc;
    packed_struct_t var_packed_struct;
    unpacked_struct_t var_unpacked_struct;
    fixed_array_t var_fixed_array;
    byte_q_t var_queue;
    int_assoc_t var_assoc;
    always_comb begin
        formatted_p_packed_struct = "";
        formatted_p_unpacked_struct = "";
        formatted_p_fixed_array = "";
        formatted_p_byte = "";
        formatted_p_int = "";
        formatted_p_queue = "";
        formatted_p_assoc = "";
        formatted_p_abbreviated_packed_struct = "";
        formatted_p_abbreviated_unpacked_struct = "";
        formatted_p_abbreviated_fixed_array = "";
        formatted_p_abbreviated_queue = "";
        formatted_p_abbreviated_assoc = "";
        var_packed_struct = const_packed_struct;
        var_unpacked_struct = const_unpacked_struct;
        var_fixed_array = const_fixed_array;
        var_queue = const_queue;
        var_assoc = const_assoc;
        if (in_byte == 0) begin
            formatted_p_packed_struct = $sformatf(format_p, var_packed_struct);
            formatted_p_unpacked_struct = $sformatf(format_p, var_unpacked_struct);
            formatted_p_fixed_array = $sformatf(format_p, var_fixed_array);
            formatted_p_byte = $sformatf(format_p, const_byte_val);
            formatted_p_int = $sformatf(format_p, const_int_val);
            formatted_p_queue = $sformatf(format_p, var_queue);
            formatted_p_assoc = $sformatf(format_p, var_assoc);
        end else begin
            var_packed_struct = const_packed_struct;
            var_unpacked_struct = const_unpacked_struct;
            var_fixed_array = const_fixed_array;
            var_queue = const_queue;
            var_assoc = const_assoc;
            formatted_p_abbreviated_packed_struct = $sformatf(format_p_abbreviated, var_packed_struct);
            formatted_p_abbreviated_unpacked_struct = $sformatf(format_p_abbreviated, var_unpacked_struct);
            formatted_p_abbreviated_fixed_array = $sformatf(format_p_abbreviated, var_fixed_array);
            formatted_p_abbreviated_queue = $sformatf(format_p_abbreviated, var_queue);
            formatted_p_abbreviated_assoc = $sformatf(format_p_abbreviated, var_assoc);
            formatted_p_byte = $sformatf(format_p, const_byte_val);
            formatted_p_int = $sformatf(format_p, const_int_val);
        end
        out_dummy = in_byte;
    end
endmodule

module EnumFormatModule (
    input logic [1:0] in_enum_val,
    output logic [31:0] out_dummy
);
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_BUSY = 2'b01,
        STATE_DONE = 2'b10
    } my_enum_t;
    localparam my_enum_t const_enum_idle = STATE_IDLE;
    localparam my_enum_t const_enum_busy = STATE_BUSY;
    localparam logic [1:0] const_value_not_in_enum = 2'b11;
    localparam string format_p = "%p";
    string formatted_p_enum_idle;
    string formatted_p_enum_busy;
    string formatted_p_enum_not_in_enum;
    always_comb begin
        formatted_p_enum_idle = "";
        formatted_p_enum_busy = "";
        formatted_p_enum_not_in_enum = "";
        if (in_enum_val == STATE_IDLE) begin
            formatted_p_enum_idle = $sformatf(format_p, const_enum_idle);
            formatted_p_enum_busy = $sformatf(format_p, const_enum_busy);
            formatted_p_enum_not_in_enum = $sformatf(format_p, const_value_not_in_enum);
        end else begin
            formatted_p_enum_idle = $sformatf(format_p, const_enum_busy);
            formatted_p_enum_busy = $sformatf(format_p, const_enum_idle);
            formatted_p_enum_not_in_enum = $sformatf(format_p, const_value_not_in_enum);
        end
        out_dummy = in_enum_val;
    end
endmodule

module MixedOptionsFormatModule (
    input int in_value,
    input string in_string,
    output logic [31:0] out_dummy
);
    localparam int int_data = 42;
    localparam real real_data = 123.45;
    localparam string string_data = "SystemVerilog";
    localparam byte byte_data = 'hAA;
    localparam logic [3:0] strength_data = 4'b1x0Z;
    localparam string format_d_width_left = "%-10d";
    localparam string format_f_precision_width = "%10.2f";
    localparam string format_s_width = "%15s";
    localparam string format_h_width_zero_pad = "%08h";
    localparam string format_g_precision = "%.3g";
    localparam string format_t_width_left = "%-20t";
    localparam string format_c = "%c";
    localparam string format_v = "%v";
    localparam string format_p = "%p";
    localparam string format_p_width = "%10p";
    typedef struct { byte x; shortint y; } simple_struct_t;
    localparam simple_struct_t struct_data = '{x: 'h11, y: 1234};
    string fmt_d_wl;
    string fmt_f_pw;
    string fmt_s_w;
    string fmt_h_wz;
    string fmt_g_p;
    string fmt_t_wl;
    string fmt_c;
    string fmt_v;
    string fmt_p;
    string fmt_p_w;
    simple_struct_t var_struct;
    always_comb begin
        fmt_d_wl = "";
        fmt_f_pw = "";
        fmt_s_w = "";
        fmt_h_wz = "";
        fmt_g_p = "";
        fmt_t_wl = "";
        fmt_c = "";
        fmt_v = "";
        fmt_p = "";
        fmt_p_w = "";
        if (in_value > 0) begin
            var_struct = struct_data;
            fmt_d_wl = $sformatf(format_d_width_left, int_data);
            fmt_f_pw = $sformatf(format_f_precision_width, real_data);
            fmt_s_w = $sformatf(format_s_width, string_data);
            fmt_h_wz = $sformatf(format_h_width_zero_pad, int_data);
            fmt_g_p = $sformatf(format_g_precision, real_data);
            fmt_t_wl = $sformatf(format_t_width_left, $time);
            fmt_c = $sformatf(format_c, byte_data);
            fmt_v = $sformatf(format_v, strength_data);
            fmt_p = $sformatf(format_p, var_struct);
            fmt_p_w = $sformatf(format_p_width, var_struct);
        end else begin
            var_struct = '{x: byte'(in_value), y: shortint'(in_value)};
            fmt_d_wl = $sformatf(format_d_width_left, in_value);
            fmt_f_pw = $sformatf(format_f_precision_width, $bitstoreal(in_value));
            fmt_s_w = $sformatf(format_s_width, in_string);
            fmt_h_wz = $sformatf(format_h_width_zero_pad, in_value);
            fmt_g_p = $sformatf(format_g_precision, $bitstoreal(in_value));
            fmt_t_wl = $sformatf(format_t_width_left, 0);
            fmt_c = $sformatf(format_c, byte'(in_value));
            fmt_v = $sformatf(format_v, in_value[3:0]);
            fmt_p = $sformatf(format_p, var_struct);
            fmt_p_w = $sformatf(format_p_width, var_struct);
        end
        out_dummy = in_value;
    end
endmodule

module ErrorTriggerModule (
    input bit in_select,
    output logic out_dummy
);
    localparam string format_missing_specifier = "Value: %";
    localparam string format_invalid_width = "%w0d";
    localparam string format_invalid_precision = "%.xd";
    localparam string format_width_not_allowed_c = "%10c";
    localparam string format_precision_not_float_d = "%.2d";
    localparam string format_zeropad_not_allowed_s = "%015s";
    localparam string format_unknown_specifier_k = "%k";
    localparam string format_unknown_specifier_A = "%A";
    localparam string format_unknown_specifier_l = "%l";
    localparam string format_unknown_specifier_m = "%m";
    localparam int data_int = 100;
    localparam byte data_byte = byte'(65);
    localparam real data_real = 5.67;
    localparam string data_string = "test";
    localparam logic [3:0] data_strength = 4'b1010;
    string fmt_err1;
    string fmt_err2;
    string fmt_err3;
    string fmt_err4;
    string fmt_err5;
    string fmt_err6;
    string fmt_err7;
    string fmt_err8;
    string fmt_err9;
    string fmt_err10;
    always_comb begin
        fmt_err1 = "";
        fmt_err2 = "";
        fmt_err3 = "";
        fmt_err4 = "";
        fmt_err5 = "";
        fmt_err6 = "";
        fmt_err7 = "";
        fmt_err8 = "";
        fmt_err9 = "";
        fmt_err10 = "";
        if (in_select) begin
            fmt_err1 = $sformatf(format_missing_specifier, data_int);
            fmt_err2 = $sformatf(format_invalid_width, data_int);
            fmt_err3 = $sformatf(format_invalid_precision, data_int);
            fmt_err4 = $sformatf(format_width_not_allowed_c, data_byte);
            fmt_err5 = $sformatf(format_precision_not_float_d, data_int);
            fmt_err6 = $sformatf(format_zeropad_not_allowed_s, data_string);
            fmt_err7 = $sformatf(format_unknown_specifier_k, data_int);
            fmt_err8 = $sformatf(format_unknown_specifier_A, data_real);
            fmt_err9 = $sformatf(format_unknown_specifier_l, data_strength);
            fmt_err10 = $sformatf(format_unknown_specifier_m, data_string);
        end else begin
            fmt_err1 = $sformatf("%d", data_int);
            fmt_err2 = $sformatf("%d", data_int);
            fmt_err3 = $sformatf("%d", data_int);
            fmt_err4 = $sformatf("%c", data_byte);
            fmt_err5 = $sformatf("%f", data_real);
            fmt_err6 = $sformatf("%s", data_string);
            fmt_err7 = $sformatf("%d", data_int);
            fmt_err8 = $sformatf("%f", data_real);
            fmt_err9 = $sformatf("%v", data_strength);
            fmt_err10 = $sformatf("%s", data_string);
        end
        out_dummy = in_select;
    end
endmodule

module PercentPercentModule (
    input logic in_bit,
    output logic out_dummy
);
    localparam string format_percent_escape = "Value: %% %d";
    localparam int data_value = 99;
    string formatted_string;
    always_comb begin
        formatted_string = "";
        if (in_bit) begin
            formatted_string = $sformatf(format_percent_escape, data_value);
        end else begin
            formatted_string = $sformatf(format_percent_escape, data_value + 1);
        end
        out_dummy = in_bit;
    end
endmodule

module VariousPadAlignModule (
    input logic [7:0] in_value,
    output logic out_dummy
);
    localparam int int_data = 5;
    localparam int large_int_data = 123456;
    localparam string string_data = "abc";
    localparam string long_string_data = "longer_string";
    localparam string format_d_width = "%5d";
    localparam string format_d_zero = "%05d";
    localparam string format_d_left = "%-5d";
    localparam string format_d_left_zero = "%-05d";
    localparam string format_s_width = "%5s";
    localparam string format_s_left = "%-5s";
    string fmt_d_w;
    string fmt_d_z;
    string fmt_d_l;
    string fmt_d_lz;
    string fmt_s_w;
    string fmt_s_l;
    always_comb begin
        fmt_d_w = "";
        fmt_d_z = "";
        fmt_d_l = "";
        fmt_d_lz = "";
        fmt_s_w = "";
        fmt_s_l = "";
        if (in_value > 10) begin
            fmt_d_w = $sformatf(format_d_width, int_data);
            fmt_d_z = $sformatf(format_d_zero, int_data);
            fmt_d_l = $sformatf(format_d_left, int_data);
            fmt_d_lz = $sformatf(format_d_left_zero, int_data);
            fmt_s_w = $sformatf(format_s_width, string_data);
            fmt_s_l = $sformatf(format_s_left, string_data);
        end else begin
            fmt_d_w = $sformatf(format_d_width, in_value);
            fmt_d_z = $sformatf(format_d_zero, large_int_data);
            fmt_d_l = $sformatf(format_d_left, in_value);
            fmt_d_lz = $sformatf(format_d_left_zero, large_int_data);
            fmt_s_w = $sformatf(format_s_width, long_string_data);
            fmt_s_l = $sformatf(format_s_left, long_string_data);
        end
        out_dummy = fmt_d_w.len();
    end
endmodule

module UnionAliasFormatModule (
    input bit in_select,
    output logic [31:0] out_dummy
);
    typedef union packed {
        logic [15:0] byte_val;
        logic [15:0] shortint_val;
    } packed_union_t;
    typedef union {
        int i;
        string s;
        real r;
    } unpacked_union_t;
    typedef packed_union_t packed_union_alias_t;
    typedef unpacked_union_t unpacked_union_alias_t;
    typedef int int_array_alias_t[2];
    localparam packed_union_t const_packed_union = 16'h0055;
    localparam packed_union_alias_t const_packed_union_alias = const_packed_union;
    localparam int_array_alias_t const_int_array_alias = '{10, 20};
    localparam packed_union_t const_packed_union_alt = 16'hABCD;
    localparam int_array_alias_t const_int_array_alias_alt = '{30, 40};
    string formatted_p_packed_union;
    string formatted_p_unpacked_union_int;
    string formatted_p_unpacked_union_str;
    string formatted_p_unpacked_union_unset;
    string formatted_p_packed_union_alias;
    string formatted_p_unpacked_union_alias;
    string formatted_p_int_array_alias;
    localparam string format_p = "%p";
    unpacked_union_t var_unpacked_union_int;
    unpacked_union_t var_unpacked_union_str;
    unpacked_union_t var_unpacked_union_unset;
    unpacked_union_alias_t var_unpacked_union_alias;
    unpacked_union_t var_unpacked_union_real;
    always_comb begin
        formatted_p_packed_union = "";
        formatted_p_unpacked_union_int = "";
        formatted_p_unpacked_union_str = "";
        formatted_p_unpacked_union_unset = "";
        formatted_p_packed_union_alias = "";
        formatted_p_unpacked_union_alias = "";
        formatted_p_int_array_alias = "";
        var_unpacked_union_int.i = 123;
        var_unpacked_union_str.s = "hello";
        if (in_select) begin
            var_unpacked_union_alias = var_unpacked_union_str;
            formatted_p_packed_union = $sformatf(format_p, const_packed_union);
            formatted_p_unpacked_union_int = $sformatf(format_p, var_unpacked_union_int);
            formatted_p_unpacked_union_str = $sformatf(format_p, var_unpacked_union_str);
            formatted_p_unpacked_union_unset = $sformatf(format_p, var_unpacked_union_unset);
            formatted_p_packed_union_alias = $sformatf(format_p, const_packed_union_alias);
            formatted_p_unpacked_union_alias = $sformatf(format_p, var_unpacked_union_alias);
            formatted_p_int_array_alias = $sformatf(format_p, const_int_array_alias);
        end else begin
            var_unpacked_union_real.r = 9.87;
            var_unpacked_union_alias = var_unpacked_union_real;
            formatted_p_packed_union = $sformatf(format_p, const_packed_union_alt);
            formatted_p_unpacked_union_int = $sformatf(format_p, var_unpacked_union_real);
            formatted_p_unpacked_union_str = $sformatf(format_p, var_unpacked_union_unset);
            formatted_p_unpacked_union_unset = $sformatf(format_p, var_unpacked_union_int);
            formatted_p_packed_union_alias = $sformatf(format_p, const_packed_union_alt);
            formatted_p_unpacked_union_alias = $sformatf(format_p, var_unpacked_union_alias);
            formatted_p_int_array_alias = $sformatf(format_p, const_int_array_alias_alt);
        end
        out_dummy = in_select;
    end
endmodule

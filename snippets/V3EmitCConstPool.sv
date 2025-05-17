module vScalarConstants (
    input int in_scalar_val,
    output longint out_scalar_result
);
    const byte CONST_BYTE = 8'hF3;
    const unsigned shortint CONST_USHORT = 16'd55555;
    const longint CONST_LONGINT = 64'hAABBCCDDEEFF0011;
    const real CONST_REAL = 3.14159;
    const shortreal CONST_SHORTREAL = -0.00123;
    const time CONST_TIME = 100ps;
    const bit [7:0] CONST_BIT_VECTOR = 8'b10101111;
    const logic CONST_BOOL = 1'b1;
    const chandle CONST_CHANDLE_NULL = null;
    const string CONST_MOD_STRING = "Module Scalar String";
    const int CONST_ZERO = 0;
    const real ANOTHER_CONST_REAL = 2.71828;
    const logic [3:0] ANOTHER_CONST_NIBBLE = 4'hC;
    const string ANOTHER_STRING_CONST = "Another Scalar String";
    const int ANOTHER_CONST_INT = 999;
    const unsigned int UNSIGN_INT_LITERAL = 12345;
    const bit [15:0] WIDE_BIT_LITERAL = 16'hFEDC;
    const integer INTEGER_LITERAL = 567;
    longint val_const_byte;
    longint val_const_ushort;
    longint val_const_longint;
    longint val_const_real_scaled;
    longint val_const_shortreal_scaled;
    longint val_const_time_scaled;
    longint val_const_bit_vector;
    longint val_const_bool;
    int val_const_mod_string_len;
    longint val_const_zero;
    longint val_another_const_int;
    longint val_another_const_real_scaled;
    longint val_another_const_nibble;
    int val_another_string_len;
    unsigned int val_unsign_int;
    longint val_wide_bit;
    int val_integer_literal;
    always_comb begin
        val_const_byte = CONST_BYTE;
        val_const_ushort = CONST_USHORT;
        val_const_longint = CONST_LONGINT;
        val_const_real_scaled = $cast(longint, CONST_REAL * 100000);
        val_const_shortreal_scaled = $cast(longint, CONST_SHORTREAL * 1000000);
        val_const_time_scaled = $cast(longint, CONST_TIME);
        val_const_bit_vector = CONST_BIT_VECTOR;
        val_const_bool = CONST_BOOL;
        val_const_mod_string_len = CONST_MOD_STRING.len();
        val_const_zero = CONST_ZERO;
        val_another_const_int = ANOTHER_CONST_INT;
        val_another_const_real_scaled = $cast(longint, ANOTHER_CONST_REAL * 100000);
        val_another_const_nibble = ANOTHER_CONST_NIBBLE;
        val_another_string_len = ANOTHER_STRING_CONST.len();
        val_unsign_int = UNSIGN_INT_LITERAL;
        val_wide_bit = WIDE_BIT_LITERAL;
        val_integer_literal = INTEGER_LITERAL;
        out_scalar_result = $cast(longint, in_scalar_val)
                          + val_const_byte + val_const_ushort + val_const_longint + val_const_real_scaled
                          + val_const_shortreal_scaled + val_const_time_scaled + val_const_bit_vector + val_const_bool
                          + val_const_mod_string_len + val_const_zero
                          + val_another_const_int + val_another_const_real_scaled + val_another_const_nibble + val_another_string_len
                          + $cast(longint, val_unsign_int) + val_wide_bit + $cast(longint, val_integer_literal);
    end
endmodule
module vAggregateConstants (
    input int in_index_sel,
    output longint out_aggregate_array_sum
);
    typedef enum bit [1:0] {
        RED = 2'b00,
        GREEN = 2'b01,
        BLUE = 2'b10,
        YELLOW = 2'b11
    } Color_e;
    typedef struct packed {
        logic [7:0] data;
        Color_e color;
        int status_code;
    } Packet_t;
    typedef struct {
        real voltage;
        int current;
    } Electrical_t;
    typedef union {
        longint ldata;
        int idata [3];
        shortreal sdata;
    } DataUnion_t;
    typedef struct packed {
        shortint indexes [2];
        logic [3:0] state_bits;
    } ControlBlock_t;
    const int CONST_PACKED_ARR [3] = '{10, 20, 30};
    const logic [15:0] CONST_UNPACKED_ARR [2] = {16'h1111, 16'h2222};
    const int CONST_MULTI_DIM_ARR [2][3] = '{'{100, 200, 300}, '{400, 500, 600}};
    const int CONST_OPEN_ARR [] = {7, 8, 9, 10};
    const logic [63:0] CONST_REPLICATE_WIDE = {8{8'hAA}};
    const logic [127:0] CONST_CONCATENATE_WIDE = {64'h1122334455667788, 64'h99AABBCCDDEEFF00};
    const string CONST_ARRAY_STRING = "Array String Constant";
    const Color_e CONST_COLOR = BLUE;
    const Packet_t CONST_PACKET = '{data: 8'hEE, color: YELLOW, status_code: 101};
    const Electrical_t CONST_ELECTRICAL = '{voltage: 5.0, current: 2};
    const DataUnion_t CONST_DATA_UNION = '{idata: '{1, 2, 3}};
    const ControlBlock_t CONST_CONTROL_BLOCK = '{indexes: '{ -5, 15}, state_bits: 4'b1101};
    const Packet_t CONST_PACKET_ARRAY [2] = '{ '{data: 8'h11, color: RED, status_code: 1}, '{data: 8'h22, color: GREEN, status_code: 2} };
    const logic [7:0] ANOTHER_CONST_2D_ARR [2][1] = '{'{8'h33}, '{8'h44}};
    const string ANOTHER_AGGREGATE_STRING = "Another Aggregate String";
    const Packet_t ANOTHER_CONST_PACKET = '{data: 8'hAA, color: GREEN, status_code: 202};
    const Color_e ANOTHER_CONST_COLOR = RED;
    const bit [7:0] BYTE_ARRAY [2] = '{8'd15, 8'd25};
    int arr_p_val, arr_lp_val;
    int arr_2d_val;
    int open_arr_val;
    longint rep_val_scaled;
    longint concat_val_low_scaled;
    int string_len_array_const;
    longint val_const_color;
    longint val_const_packet_data, val_const_packet_color, val_const_packet_status;
    longint val_const_electrical_volt_scaled, val_const_electrical_current;
    longint val_const_data_union_elem;
    longint val_const_control_index, val_const_control_state;
    longint val_const_packet_arr_data, val_const_packet_arr_status;
    int another_arr_2d_val;
    int another_aggregate_string_len;
    longint val_another_const_packet_data, val_another_const_packet_color, val_another_const_packet_status;
    longint val_another_const_color;
    int byte_array_val;
    always_comb begin
        arr_p_val = CONST_PACKED_ARR[in_index_sel % $size(CONST_PACKED_ARR)];
        arr_lp_val = CONST_UNPACKED_ARR[in_index_sel % $size(CONST_UNPACKED_ARR)];
        arr_2d_val = CONST_MULTI_DIM_ARR[in_index_sel % $size(CONST_MULTI_DIM_ARR, 1)][in_index_sel % $size(CONST_MULTI_DIM_ARR, 2)];
        if ($cast(int, in_index_sel % $size(CONST_OPEN_ARR)) < $size(CONST_OPEN_ARR)) begin
             open_arr_val = CONST_OPEN_ARR[in_index_sel % $size(CONST_OPEN_ARR)];
        end else begin
             open_arr_val = '0;
        end
        rep_val_scaled = $cast(longint, CONST_REPLICATE_WIDE) / 1000;
        concat_val_low_scaled = $cast(longint, CONST_CONCATENATE_WIDE[63:0]) / 1000;
        string_len_array_const = CONST_ARRAY_STRING.len();
        val_const_color = CONST_COLOR;
        val_const_packet_data = CONST_PACKET.data;
        val_const_packet_color = CONST_PACKET.color;
        val_const_packet_status = CONST_PACKET.status_code;
        val_const_electrical_volt_scaled = $cast(longint, CONST_ELECTRICAL.voltage * 1000);
        val_const_electrical_current = CONST_ELECTRICAL.current;
        case (in_index_sel % 3)
            0: val_const_data_union_elem = CONST_DATA_UNION.idata[0];
            1: val_const_data_union_elem = CONST_DATA_UNION.idata[1];
            2: val_const_data_union_elem = CONST_DATA_UNION.idata[2];
            default: val_const_data_union_elem = 0;
        endcase
        val_const_control_index = CONST_CONTROL_BLOCK.indexes[in_index_sel % $size(CONST_CONTROL_BLOCK.indexes)];
        val_const_control_state = CONST_CONTROL_BLOCK.state_bits;
        val_const_packet_arr_data = CONST_PACKET_ARRAY[in_index_sel % $size(CONST_PACKET_ARRAY)].data;
        val_const_packet_arr_status = CONST_PACKET_ARRAY[in_index_sel % $size(CONST_PACKET_ARRAY)].status_code;
        another_arr_2d_val = ANOTHER_CONST_2D_ARR[in_index_sel % $size(ANOTHER_CONST_2D_ARR, 1)][0];
        another_aggregate_string_len = ANOTHER_AGGREGATE_STRING.len();
        val_another_const_packet_data = ANOTHER_CONST_PACKET.data;
        val_another_const_packet_color = ANOTHER_CONST_PACKET.color;
        val_another_const_packet_status = ANOTHER_CONST_PACKET.status_code;
        val_another_const_color = ANOTHER_CONST_COLOR;
        byte_array_val = BYTE_ARRAY[in_index_sel % $size(BYTE_ARRAY)];
        out_aggregate_array_sum = $cast(longint, in_index_sel) +
                                  $cast(longint, arr_p_val) + $cast(longint, arr_lp_val) + $cast(longint, arr_2d_val) +
                                  $cast(longint, open_arr_val) + rep_val_scaled + concat_val_low_scaled +
                                  $cast(longint, string_len_array_const) +
                                  val_const_color + val_const_packet_data + val_const_packet_color + val_const_packet_status +
                                  val_const_electrical_volt_scaled + val_const_electrical_current + val_const_data_union_elem +
                                  val_const_control_index + val_const_control_state +
                                  val_const_packet_arr_data + val_const_packet_arr_status +
                                  $cast(longint, another_arr_2d_val) + $cast(longint, another_aggregate_string_len) +
                                  val_another_const_packet_data + val_another_const_packet_color + val_another_const_packet_status +
                                  val_another_const_color + $cast(longint, byte_array_val);
    end
endmodule
module vExpressionConstants (
    input int in_expr_input,
    output int out_expr_output
);
    parameter int PA = 30;
    parameter int PB = 7;
    parameter real PR = 10.0;
    const int CONST_ADD = PA + PB;
    const int CONST_SUB = PA - PB;
    const int CONST_MUL = PA * PB;
    const int CONST_DIV = PA / PB;
    const real CONST_REAL_DIV = $cast(real, PA) / PB;
    const int CONST_MOD = PA % PB;
    const real CONST_ADD_REAL = PR + CONST_REAL_DIV;
    const real CONST_SCIENTIFIC_REAL = 1.23e-4;
    const logic [7:0] CONST_BIT_UNARY_NOT = ~8'h5A;
    const logic [7:0] CONST_BIT_AND = 8'hF0 & 8'hA5;
    const logic [7:0] CONST_BIT_OR = 8'h11 | 8'h22;
    const logic [7:0] CONST_BIT_XOR = 8'h33 ^ 8'hFF;
    const logic CONST_REDUCTION_AND = &8'h01;
    const logic CONST_REDUCTION_OR = |8'hF0;
    const logic CONST_REDUCTION_XOR = ^8'hAA;
    const logic CONST_REDUCTION_NAND = ~&8'h01;
    const logic CONST_REDUCTION_NOR = ~|8'hF0;
    const logic CONST_REDUCTION_XNOR = ~^8'hAA;
    const logic [15:0] CONST_SHIFT_L = 16'h1234 << 3;
    const logic [15:0] CONST_SHIFT_R = 16'hABCD >> 5;
    const int CONST_ARITH_SHIFT_R = $signed(32'hFFFFA000) >>> 9;
    const int CONST_SHIFT_VAR = 32'd100 << PA%5; 
    const int CONST_NEGATE = -(CONST_SUB);
    const logic CONST_LOGIC_NOT = !(CONST_MOD == 0);
    const logic CONST_LOGIC_AND = (CONST_ADD > 35) && (CONST_MUL < 250);
    const logic CONST_LOGIC_OR = (CONST_DIV < 2) || (CONST_REAL_DIV > 4.0);
    const logic CONST_EQUAL = (PA == PB);
    const logic CONST_NOT_EQUAL = (PA != PB);
    const logic CONST_CASE_EQUAL = (4'hF === 4'hX);
    const logic CONST_CASE_NOT_EQUAL = (4'hF !== 4'hX);
    const logic CONST_LESS = (PA < PB);
    const logic CONST_LESS_EQUAL = (PA <= PB);
    const logic CONST_GREATER = (PA > PB);
    const logic CONST_GREATER_EQUAL = (PA >= PB);
    const int CONST_TERNARY = (PA > PB) ? CONST_ADD : CONST_SUB;
    const logic [7:0] CONST_PART_SELECT_EXPR = 16'h5A6B [7:0];
    const logic [15:0] CONST_INDEXED_PART_SELECT = 32'hFACE1234 [15 +: 16];
    const logic [7:0] CONST_INDEXED_PART_SELECT2 = 32'hFACE1234 [15 -: 8];
    const logic [15:0] CONST_CONCAT = {8'h12, 8'h34};
    const logic [7:0] CONST_REPLICATION = {4{2'b10}};
    const logic [10:0] CONST_NESTED_CONCAT_REP = { {2{1'b1}}, 3'b010, {4{2'b11}} };
    const logic [5:0] CONST_REPLICATION2 = {(PB-4){2'b01}}; 
    const int CONST_CLOG2 = $clog2(256);
    const real CONST_SQRT = $sqrt(225.0);
    const real CONST_LOG = $log(100.0); 
    const real CONST_LOG10 = $log10(100.0);
    const int CONST_SIGNED_CAST = $signed(32'h80000000);
    const unsigned int CONST_UNSIGNED_CAST = unsigned'(32'hFFFFFFFF);
    const real CONST_CAST_REAL = real'(3.14);
    const int CONST_CAST_INT = int'(CONST_REAL_DIV);
    const bit [15:0] CONST_BIT_CAST = 16'($signed(32'hFFFF0000));
    const longint CONST_LONGINT_CAST = longint'(1000);
    const int CONST_INT_FROM_REAL = $cast(int, 5.6);
    const logic [7:0] CONST_SIZED = 8'(255);
    const bit [15:0] CONST_SIZED_WIDE = 16'(300);
    parameter logic [7:0] ARRAY_FOR_PROPS [4];
    const int CONST_SIZE = $size(CONST_REPLICATION);
    const int CONST_BITS = $bits(CONST_REPLICATION);
    const int CONST_LEFT = $left(ARRAY_FOR_PROPS, 1);
    const int CONST_RIGHT = $right(ARRAY_FOR_PROPS, 1);
    const int CONST_LOW = $low(ARRAY_FOR_PROPS, 1);
    const int CONST_HIGH = $high(ARRAY_FOR_PROPS, 1);
    const int CONST_INCREMENT = $increment(ARRAY_FOR_PROPS, 1);
    const int CONST_DIMENSION_SIZE = $size(CONST_MULTI_DIM_ARR, 2);
    const int CONST_DIMENSION_LEFT = $left(CONST_MULTI_DIM_ARR, 2);
    const string CONST_EXPR_STRING = "Expression Constant";
    const string CONST_CONCAT_STRING = CONST_EXPR_STRING + " Concatenation";
    const string CONST_REPLICATE_STRING = {2{CONST_EXPR_STRING}};
    const string CONST_STRING_LITERAL = "Just a string literal";
    const int ANOTHER_CONST_BIT_OPS = $cast(int, CONST_BIT_AND ^ CONST_BIT_OR);
    const int ANOTHER_CONST_REDUCTION_OPS = CONST_REDUCTION_AND + CONST_REDUCTION_OR + CONST_REDUCTION_XOR + CONST_REDUCTION_NAND + CONST_REDUCTION_NOR + CONST_REDUCTION_XNOR;
    const int ANOTHER_CONST_SHIFTS = $cast(int, CONST_SHIFT_L >> 8) + $cast(int, CONST_SHIFT_R << 2) + CONST_ARITH_SHIFT_R + CONST_SHIFT_VAR;
    const int ANOTHER_CONST_LOGIC_OPS = CONST_LOGIC_NOT + CONST_LOGIC_AND + CONST_LOGIC_OR + CONST_EQUAL + CONST_NOT_EQUAL + CONST_CASE_EQUAL + CONST_CASE_NOT_EQUAL + CONST_LESS + CONST_LESS_EQUAL + CONST_GREATER + CONST_GREATER_EQUAL;
    const real ANOTHER_CONST_MATH = $log10(1000.0);
    const int ANOTHER_CONST_TERNARY = (CONST_DIV == 0) ? 1 : 0;
    const int ANOTHER_CONST_SIZE_BITS = $size(ANOTHER_CONST_BIT_OPS) + $bits(ANOTHER_CONST_BIT_OPS);
    const string ANOTHER_EXPR_STRING = "Another Expression String";
    int val_const_add, val_const_sub, val_const_mul, val_const_div, val_const_mod, val_const_real_div_scaled, val_const_add_real_scaled, val_const_scientific_real_scaled;
    int val_const_bit_unary, val_const_bit_and, val_const_bit_or, val_const_bit_xor;
    int val_red_and, val_red_or, val_red_xor, val_red_nand, val_red_nor, val_red_xnor;
    int val_const_shift_l, val_const_shift_r, val_const_arith_shift_r, val_const_shift_var;
    int val_const_negate, val_const_logic_not, val_const_logic_and, val_const_logic_or, val_const_equal, val_const_not_equal, val_const_case_equal, val_const_case_not_equal, val_const_less, val_const_less_equal, val_const_greater, val_const_greater_equal;
    int val_const_ternary;
    int val_const_part_select, val_const_indexed_part_select, val_const_indexed_part_select2;
    int val_const_concat, val_const_replication, val_const_nested_concat_rep, val_const_replication2;
    int val_const_clog2, val_const_sqrt_scaled, val_const_log_scaled, val_const_log10_scaled, val_const_signed_cast, val_const_unsigned_cast, val_const_cast_int, val_const_cast_real_scaled, val_const_bit_cast_scaled, val_const_longint_cast, val_const_int_from_real;
    int val_const_sized, val_const_sized_wide;
    int val_const_size, val_const_bits, val_const_left, val_const_right, val_const_low, val_const_high, val_const_increment, val_const_dimension_size, val_const_dimension_left;
    int val_const_expr_string_len, val_const_concat_string_len, val_const_replicate_string_len, val_const_string_literal_len;
    int val_another_const_bit_ops, val_another_const_red_ops, val_another_const_shifts, val_another_const_logic_ops, val_another_const_math_scaled, val_another_const_ternary;
    int val_another_const_size_bits;
    int val_another_expr_string_len;
    always_comb begin
        val_const_add = CONST_ADD;
        val_const_sub = CONST_SUB;
        val_const_mul = CONST_MUL;
        val_const_div = CONST_DIV;
        val_const_real_div_scaled = $cast(int, CONST_REAL_DIV * 1000);
        val_const_mod = CONST_MOD;
        val_const_add_real_scaled = $cast(int, CONST_ADD_REAL * 1000);
        val_const_scientific_real_scaled = $cast(int, CONST_SCIENTIFIC_REAL * 1e6); 
        val_const_bit_unary = CONST_BIT_UNARY_NOT;
        val_const_bit_and = CONST_BIT_AND;
        val_const_bit_or = CONST_BIT_OR;
        val_const_bit_xor = CONST_BIT_XOR;
        val_red_and = CONST_REDUCTION_AND;
        val_red_or = CONST_REDUCTION_OR;
        val_red_xor = CONST_REDUCTION_XOR;
        val_red_nand = CONST_REDUCTION_NAND;
        val_red_nor = CONST_REDUCTION_NOR;
        val_red_xnor = CONST_REDUCTION_XNOR;
        val_const_shift_l = CONST_SHIFT_L;
        val_const_shift_r = CONST_SHIFT_R;
        val_const_arith_shift_r = CONST_ARITH_SHIFT_R;
        val_const_shift_var = CONST_SHIFT_VAR;
        val_const_negate = CONST_NEGATE;
        val_const_logic_not = CONST_LOGIC_NOT;
        val_const_logic_and = CONST_LOGIC_AND;
        val_const_logic_or = CONST_LOGIC_OR;
        val_const_equal = CONST_EQUAL;
        val_const_not_equal = CONST_NOT_EQUAL;
        val_const_case_equal = CONST_CASE_EQUAL;
        val_const_case_not_equal = CONST_CASE_NOT_EQUAL;
        val_const_less = CONST_LESS;
        val_const_less_equal = CONST_LESS_EQUAL;
        val_const_greater = CONST_GREATER;
        val_const_greater_equal = CONST_GREATER_EQUAL;
        val_const_ternary = CONST_TERNARY;
        val_const_part_select = $cast(int, CONST_PART_SELECT_EXPR);
        val_const_indexed_part_select = $cast(int, CONST_INDEXED_PART_SELECT);
        val_const_indexed_part_select2 = $cast(int, CONST_INDEXED_PART_SELECT2);
        val_const_concat = $cast(int, CONST_CONCAT);
        val_const_replication = $cast(int, CONST_REPLICATION);
        val_const_nested_concat_rep = $cast(int, CONST_NESTED_CONCAT_REP);
        val_const_replication2 = $cast(int, CONST_REPLICATION2);
        val_const_clog2 = CONST_CLOG2;
        val_const_sqrt_scaled = $cast(int, CONST_SQRT * 10);
        val_const_log_scaled = $cast(int, CONST_LOG * 1000);
        val_const_log10_scaled = $cast(int, CONST_LOG10 * 1000);
        val_const_signed_cast = CONST_SIGNED_CAST;
        val_const_unsigned_cast = $cast(int, CONST_UNSIGNED_CAST);
        val_const_cast_int = CONST_CAST_INT;
        val_const_cast_real_scaled = $cast(int, CONST_CAST_REAL * 1000);
        val_const_bit_cast_scaled = $cast(int, CONST_BIT_CAST);
        val_const_longint_cast = $cast(int, CONST_LONGINT_CAST);
        val_const_int_from_real = CONST_INT_FROM_REAL;
        val_const_sized = CONST_SIZED;
        val_const_sized_wide = $cast(int, CONST_SIZED_WIDE);
        val_const_size = CONST_SIZE;
        val_const_bits = CONST_BITS;
        val_const_left = CONST_LEFT;
        val_const_right = CONST_RIGHT;
        val_const_low = CONST_LOW;
        val_const_high = CONST_HIGH;
        val_const_increment = CONST_INCREMENT;
        val_const_dimension_size = CONST_DIMENSION_SIZE;
        val_const_dimension_left = CONST_DIMENSION_LEFT;
        val_const_expr_string_len = CONST_EXPR_STRING.len();
        val_const_concat_string_len = CONST_CONCAT_STRING.len();
        val_const_replicate_string_len = CONST_REPLICATE_STRING.len();
        val_const_string_literal_len = CONST_STRING_LITERAL.len();
        val_another_const_bit_ops = ANOTHER_CONST_BIT_OPS;
        val_another_const_red_ops = ANOTHER_CONST_REDUCTION_OPS;
        val_another_const_shifts = ANOTHER_CONST_SHIFTS;
        val_another_const_logic_ops = ANOTHER_CONST_LOGIC_OPS;
        val_another_const_math_scaled = $cast(int, ANOTHER_CONST_MATH * 1000); 
        val_another_const_ternary = ANOTHER_CONST_TERNARY;
        val_another_const_size_bits = ANOTHER_CONST_SIZE_BITS;
        val_another_expr_string_len = ANOTHER_EXPR_STRING.len();
        out_expr_output = in_expr_input
                        + val_const_add + val_const_sub + val_const_mul + val_const_div + val_const_mod + val_const_real_div_scaled + val_const_add_real_scaled + val_const_scientific_real_scaled
                        + val_const_bit_unary + val_const_bit_and + val_const_bit_or + val_const_bit_xor
                        + val_red_and + val_red_or + val_red_xor + val_red_nand + val_red_nor + val_red_xnor
                        + val_const_shift_l + val_const_shift_r + val_const_arith_shift_r + val_const_shift_var
                        + val_const_negate + val_const_logic_not + val_const_logic_and + val_const_logic_or + val_const_equal + val_const_not_equal + val_const_case_equal + val_const_case_not_equal + val_const_less + val_const_less_equal + val_const_greater + val_const_greater_equal
                        + val_const_ternary + val_const_part_select + val_const_indexed_part_select + val_const_indexed_part_select2 + val_const_concat + val_const_replication + val_const_nested_concat_rep + val_const_replication2
                        + val_const_clog2 + val_const_sqrt_scaled + val_const_log_scaled + val_const_log10_scaled + val_const_signed_cast + val_const_unsigned_cast + val_const_cast_int + val_const_cast_real_scaled + val_const_bit_cast_scaled + val_const_longint_cast + val_const_int_from_real
                        + val_const_sized + val_const_sized_wide
                        + val_const_size + val_const_bits + val_const_left + val_const_right + val_const_low + val_const_high + val_const_increment + val_const_dimension_size + val_const_dimension_left + val_const_expr_string_len + val_const_concat_string_len + val_const_replicate_string_len + val_const_string_literal_len
                        + val_another_const_bit_ops + val_another_const_red_ops + val_another_const_shifts + val_another_const_logic_ops + val_another_const_math_scaled + val_another_const_ternary + val_another_const_size_bits + val_another_expr_string_len;
    end
endmodule
module vStaticClassConstants (
    input int in_static_input,
    output int out_static_output
);
    class MyStaticConstClass;
        static const int STATIC_INT_CONST = 42;
        static const logic [7:0] STATIC_BYTE_CONST = 8'hAB;
        static const real STATIC_REAL_CONST = 1.618;
        static const string STATIC_STRING_CONST = "ClassStaticString";
        static const int STATIC_ARRAY_CONST [2] = '{1000, 2000};
        static const struct packed { bit a; int b; } STATIC_STRUCT_CONST = '{a: 1'b1, b: 55};
        static const int STATIC_EXPR_CONST = STATIC_INT_CONST + 10;
        static const logic STATIC_LOGIC_CONST = (STATIC_BYTE_CONST > 8'hA0);
        static const real STATIC_MATH_CONST = $sqrt(STATIC_INT_CONST * 4.0);
        static const bit [15:0] STATIC_CONCAT_CONST = {STATIC_BYTE_CONST, 8'hCD};
        static const logic STATIC_REDUCTION_CONST = &STATIC_BYTE_CONST;
    endclass
    int val_static_int;
    int val_static_byte;
    int val_static_real_scaled;
    int val_static_string_len;
    int val_static_array_elem;
    int val_static_struct_b;
    int val_static_expr;
    int val_static_logic;
    int val_static_math_scaled;
    int val_static_concat_scaled;
    int val_static_reduction;
    always_comb begin
        val_static_int = MyStaticConstClass::STATIC_INT_CONST;
        val_static_byte = MyStaticConstClass::STATIC_BYTE_CONST;
        val_static_real_scaled = $cast(int, MyStaticConstClass::STATIC_REAL_CONST * 1000);
        val_static_string_len = MyStaticConstClass::STATIC_STRING_CONST.len();
        val_static_array_elem = MyStaticConstClass::STATIC_ARRAY_CONST[in_static_input % $size(MyStaticConstClass::STATIC_ARRAY_CONST)];
        val_static_struct_b = MyStaticConstClass::STATIC_STRUCT_CONST.b;
        val_static_expr = MyStaticConstClass::STATIC_EXPR_CONST;
        val_static_logic = MyStaticConstClass::STATIC_LOGIC_CONST;
        val_static_math_scaled = $cast(int, MyStaticConstClass::STATIC_MATH_CONST * 100);
        val_static_concat_scaled = $cast(int, MyStaticConstClass::STATIC_CONCAT_CONST);
        val_static_reduction = MyStaticConstClass::STATIC_REDUCTION_CONST;
        out_static_output = in_static_input
                          + val_static_int
                          + val_static_byte
                          + val_static_real_scaled
                          + val_static_string_len
                          + val_static_array_elem
                          + val_static_struct_b
                          + val_static_expr
                          + val_static_logic
                          + val_static_math_scaled
                          + val_static_concat_scaled
                          + val_static_reduction;
    end
endmodule

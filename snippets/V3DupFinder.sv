module sv_arithmetic_ops (
    input logic [7:0] op_a,
    input logic [7:0] op_b,
    output logic [8:0] res_add,
    output logic [8:0] res_sub,
    output logic [15:0] res_mul
);
    assign res_add = op_a + op_b;
    assign res_sub = op_a - op_b;
    assign res_mul = $unsigned({8'b0, op_a}) * $unsigned({8'b0, op_b});
endmodule
module sv_bitwise_ops (
    input logic [15:0] data_x,
    input logic [15:0] data_y,
    output logic [15:0] out_and,
    output logic [15:0] out_or,
    output logic [15:0] out_xor,
    output logic [15:0] out_not_x
);
    assign out_and = data_x & data_y;
    assign out_or = data_x | data_y;
    assign out_xor = data_x ^ data_y;
    assign out_not_x = ~data_x;
endmodule
module sv_shift_ops (
    input logic [7:0] input_data,
    input logic [2:0] shift_amount,
    output logic [7:0] shifted_left,
    output logic [7:0] shifted_right_logical,
    output logic [7:0] shifted_right_arithmetic
);
    assign shifted_left = input_data << shift_amount;
    assign shifted_right_logical = input_data >> shift_amount;
    assign shifted_right_arithmetic = $signed(input_data) >>> shift_amount;
endmodule
module sv_comparison_ops (
    input logic [7:0] val1,
    input logic [7:0] val2,
    output logic is_equal,
    output logic is_not_equal,
    output logic is_greater,
    output logic is_less,
    output logic is_greater_equal,
    output logic is_less_equal
);
    assign is_equal = (val1 == val2);
    assign is_not_equal = (val1 != val2);
    assign is_greater = (val1 > val2);
    assign is_less = (val1 < val2);
    assign is_greater_equal = (val1 >= val2);
    assign is_less_equal = (val1 <= val2);
endmodule
module sv_unary_reduction_ops (
    input logic [7:0] input_vec,
    output logic [7:0] negated_vec,
    output logic [7:0] bitwise_inverted_vec,
    output logic logical_inverted_vec,
    output logic reduction_or_vec,
    output logic reduction_and_vec
);
    assign negated_vec = -input_vec;
    assign bitwise_inverted_vec = ~input_vec;
    assign logical_inverted_vec = !input_vec;
    assign reduction_or_vec = |input_vec;
    assign reduction_and_vec = &input_vec;
endmodule
module sv_concat_rep_slice (
    input logic [3:0] small_part,
    input logic [7:0] medium_part,
    input logic [31:0] large_word,
    output logic [17:0] combined_output,
    output logic [7:0] middle_byte,
    output logic lowest_bit
);
    assign combined_output = {{2{small_part}}, medium_part, 4'b0101};
    assign middle_byte = large_word[15:8];
    assign lowest_bit = large_word[0];
endmodule
module sv_conditional_operator (
    input logic condition,
    input logic [15:0] option_true,
    input logic [15:0] option_false,
    output logic [15:0] muxed_output
);
    assign muxed_output = condition ? option_true : option_false;
endmodule
module sv_procedural_case (
    input logic [1:0] select_in,
    input logic [7:0] data_0, data_1, data_2, data_3,
    output logic [7:0] case_selected_data
);
    always_comb begin
        case (select_in)
            2'b00: case_selected_data = data_0;
            2'b01: case_selected_data = data_1;
            2'b10: case_selected_data = data_2;
            default: case_selected_data = data_3;
        endcase
    end
endmodule
module sv_nested_procedural_logic (
    input logic [1:0] mode_setting,
    input logic enable_processing,
    input logic [3:0] value_a, value_b,
    output logic [3:0] operation_result
);
    always_comb begin
        if (enable_processing) begin
            case (mode_setting)
                2'b00: operation_result = value_a + value_b;
                2'b01: begin
                    if (value_a > value_b) operation_result = value_a - value_b;
                    else operation_result = value_b - value_a;
                end
                default: operation_result = value_a | value_b;
            endcase
        end else begin
            operation_result = 4'bxxxx;
        end
    end
endmodule
module sv_packed_struct_access (
    input logic [15:0] input_packed,
    output logic [7:0] byte_L_shifted,
    output logic [7:0] byte_H_xor_byte_L
);
    typedef struct packed {
        logic [7:0] lo_byte;
        logic [7:0] hi_byte;
    } byte_pair_t;
    byte_pair_t unpacked_value;
    assign unpacked_value = input_packed;
    assign byte_L_shifted = unpacked_value.lo_byte << 1;
    assign byte_H_xor_byte_L = unpacked_value.hi_byte ^ unpacked_value.lo_byte;
endmodule
module sv_array_access (
    input logic [7:0] data_elements [0:3],
    input logic [1:0] index_a, index_b,
    output logic [7:0] indexed_addition,
    output logic [7:0] fixed_indexed_xor
);
    assign indexed_addition = data_elements[index_a] + data_elements[index_b];
    assign fixed_indexed_xor = data_elements[1] ^ data_elements[2];
endmodule
module sv_enum_case (
    input logic [1:0] status_id,
    input logic [7:0] data_input,
    output logic [7:0] status_dependent_output
);
    typedef enum logic [1:0] { STATE_IDLE = 2'b00, STATE_ACTIVE = 2'b01, STATE_FINISH = 2'b10, STATE_ERROR = 2'b11 } processing_state_t;
    processing_state_t current_state;
    always_comb begin
        current_state = processing_state_t'(status_id);
        case (current_state)
            STATE_IDLE: status_dependent_output = 8'h00;
            STATE_ACTIVE: status_dependent_output = data_input + 8'h01;
            STATE_FINISH: status_dependent_output = data_input & 8'hF0;
            STATE_ERROR: status_dependent_output = 8'hFF;
            default: status_dependent_output = 8'hZZ;
        endcase
    end
endmodule
module sv_for_loop_summation (
    input logic [7:0] input_values [0:7],
    output logic [10:0] cumulative_sum
);
    always_comb begin
        cumulative_sum = 11'b0;
        for (int i = 0; i < 8; i++) begin
            cumulative_sum = cumulative_sum + $unsigned({3'b0, input_values[i]});
        end
    end
endmodule
module sv_logical_boolean_ops (
    input logic flag_A,
    input logic flag_B,
    input logic flag_C,
    output logic result_AND,
    output logic result_OR,
    output logic result_complex_logic
);
    assign result_AND = flag_A && flag_B;
    assign result_OR = flag_A || flag_B;
    assign result_complex_logic = (flag_A && !flag_B) || flag_C;
endmodule
module sv_repeated_expression_shared_signal (
    input logic [7:0] term_X, term_Y, term_Z,
    output logic [15:0] res_P, res_Q
);
    logic [15:0] common_value;
    assign common_value = $unsigned({8'b0, term_X}) + $unsigned({8'b0, term_Y});
    assign res_P = common_value * $unsigned({8'b0, term_Z}) + 16'hABCD;
    assign res_Q = common_value * $unsigned({8'b0, term_Z}) - 16'hEF01;
endmodule
module sv_repeated_conditional_patterns (
    input logic condition_S,
    input logic [7:0] option1, option2, mask_value,
    output logic [7:0] output_U, output_V
);
    logic [7:0] selected_data;
    assign selected_data = condition_S ? option1 : option2;
    assign output_U = selected_data & mask_value;
    assign output_V = selected_data | mask_value;
endmodule
module sv_repeated_procedural_calc (
    input logic enable_op,
    input logic [3:0] val_1, val_2, val_3,
    output logic [3:0] out_X, out_Y
);
    logic [3:0] temp_result;
    always_comb begin
        if (enable_op) begin
            temp_result = (val_1 + val_2) ^ val_3;
        end else begin
            temp_result = (val_1 & val_2) | val_3;
        end
        out_X = temp_result + 4'h1;
        out_Y = temp_result - 4'h1;
    end
endmodule
module sv_similar_struct_expressions (
    input logic [7:0] field_a1, field_b1, field_c1, field_d1,
    output logic [7:0] result_A, result_B
);
    assign result_A = (field_a1 | field_b1) & (field_c1 ^ field_d1);
    assign result_B = (field_a1 & field_b1) | (field_c1 ~^ field_d1);
endmodule
module sv_chained_operation_sequence (
    input logic [7:0] input_first, input_second, input_third,
    output logic [7:0] final_output
);
    logic [7:0] intermediate_step;
    assign intermediate_step = (input_first >> 2) + (input_second << 2);
    assign final_output = intermediate_step ^ (intermediate_step & input_third);
endmodule
module sv_signed_unsigned_mixing (
    input logic signed [7:0] signed_in,
    input logic        [7:0] unsigned_in,
    output logic signed [8:0] mixed_sum,
    output logic        [7:0] mixed_AND
);
    assign mixed_sum = signed_in + $signed(unsigned_in);
    assign mixed_AND = $unsigned(signed_in) & unsigned_in;
endmodule
module sv_complex_common_subexpression (
    input logic [7:0] in_a, in_b, in_c, in_d,
    output logic [7:0] out_delta, out_epsilon
);
    logic [7:0] common_sub_expr;
    assign common_sub_expr = (in_a ^ in_b) | (in_c & in_d);
    assign out_delta = common_sub_expr + 8'hEE;
    assign out_epsilon = common_sub_expr - 8'hDD;
endmodule
module sv_nested_conditional_common (
    input logic cond_X, cond_Y,
    input logic [7:0] data_alpha, data_beta, data_gamma,
    output logic [7:0] result_psi, result_chi
);
    logic [7:0] nested_selected_value;
    assign nested_selected_value = cond_X ? (cond_Y ? data_alpha : data_beta) : data_gamma;
    assign result_psi = nested_selected_value & 8'hF0;
    assign result_chi = nested_selected_value | 8'h0F;
endmodule
module sv_macro_style_expression (
    input logic [7:0] param1, param2, param3,
    output logic [7:0] res_func1, res_func2
);
    logic [7:0] macro_part;
    assign macro_part = (param1 & param2) >> 1;
    assign res_func1 = macro_part ^ param3;
    assign res_func2 = macro_part | param3;
endmodule
module sv_hash_distribution_like_logic (
    input logic [7:0] val_I,
    input logic [7:0] val_J,
    input logic [7:0] val_K,
    output logic [7:0] bucket_output
);
    logic [3:0] hash_bin_index;
    always_comb begin
        hash_bin_index = (((val_I + val_J) ^ val_K) >> 3) & 4'hF;
        case (hash_bin_index)
            4'h0: bucket_output = val_I + val_J;
            4'h1: bucket_output = val_J - val_K;
            4'h2: bucket_output = val_K & val_I;
            4'h3: bucket_output = val_J | val_K;
            4'h4: bucket_output = val_I ^ val_J;
            4'h5: bucket_output = ~val_K;
            4'h6: bucket_output = val_I << 1;
            4'h7: bucket_output = val_J >> 1;
            4'h8: bucket_output = {val_I[3:0], val_K[3:0]};
            4'h9: bucket_output = {val_J[3:0], val_I[3:0]};
            4'hA: bucket_output = val_I ^ val_J ^ val_K;
            4'hB: bucket_output = (val_I | val_J) & val_K;
            4'hC: bucket_output = (val_I & val_J) | val_K;
            4'hD: bucket_output = (|val_J) ? val_I : val_K;
            4'hE: bucket_output = (&val_K) ? val_J : val_I;
            4'hF: bucket_output = val_I;
            default: bucket_output = 8'hXX;
        endcase
    end
endmodule
module sv_struct_field_comparison (
    input logic [15:0] input_word_A,
    input logic [15:0] input_word_B,
    output logic fields_match_direct,
    output logic fields_match_swapped
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
    } two_bytes_t;
    two_bytes_t bytes_A;
    two_bytes_t bytes_B;
    always_comb begin
        bytes_A.byte0 = input_word_A[7:0];
        bytes_A.byte1 = input_word_A[15:8];
        bytes_B.byte0 = input_word_B[7:0];
        bytes_B.byte1 = input_word_B[15:8];
        if ((bytes_A.byte0 == bytes_B.byte0) && (bytes_A.byte1 == bytes_B.byte1)) begin
            fields_match_direct = 1;
        end else begin
            fields_match_direct = 0;
        end
        if ((bytes_A.byte0 == bytes_B.byte1) && (bytes_A.byte1 == bytes_B.byte0)) begin
            fields_match_swapped = 1;
        end else begin
            fields_match_swapped = 0;
        end
    end
endmodule
module sv_complex_loop_accumulator (
    input logic [3:0] weights [0:3],
    input logic [7:0] base_data,
    output logic [15:0] scaled_accumulate
);
    always_comb begin
        scaled_accumulate = 16'b0;
        for (int idx = 0; idx < 4; idx++) begin
            scaled_accumulate = scaled_accumulate + ($unsigned({8'b0, weights[idx]}) * $unsigned({8'b0, base_data}));
        end
    end
endmodule
module sv_array_of_structs_access (
    input logic [15:0] data_items [0:1],
    input logic select_index,
    output logic [7:0] selected_item_sum,
    output logic [7:0] cross_item_check
);
    typedef struct packed {
        logic [7:0] low_byte;
        logic [7:0] high_byte;
    } item_bytes_t;
    item_bytes_t items[0:1];
    assign items[0] = data_items[0];
    assign items[1] = data_items[1];
    assign selected_item_sum = items[select_index].low_byte + items[select_index].high_byte;
    assign cross_item_check = (items[0].low_byte ^ items[1].low_byte) & (items[0].high_byte | items[1].high_byte);
endmodule
module sv_complex_conditional_comparison (
    input logic [7:0] var_a, var_b, var_c, var_d,
    input logic enable_condition_Z,
    output logic is_match_pattern
);
    assign is_match_pattern = ((var_a ^ var_b) == (var_c ^ var_d)) &&
                              (enable_condition_Z ? ((var_a | var_c) == (var_b | var_d)) : 1'b1) &&
                              ((var_a & var_b) == (var_c & var_d));
endmodule
module sv_repeated_assignment_simple (
    input logic [7:0] in_w1, in_w2, in_w3, in_w4,
    output logic [7:0] out_v1, out_v2, out_v3, out_v4
);
    logic [7:0] shared_simple_calc;
    assign shared_simple_calc = in_w1 + in_w2;
    assign out_v1 = shared_simple_calc;
    assign out_v2 = shared_simple_calc;
    assign out_v3 = shared_simple_calc;
    assign out_v4 = shared_simple_calc;
endmodule
module sv_repeated_assignment_complex (
    input logic [7:0] data_i1, data_j1, data_k1, data_l1,
    input logic [7:0] data_i2, data_j2, data_k2, data_l2,
    output logic [7:0] result_R, result_S
);
    logic [7:0] common_complex_sub;
    assign common_complex_sub = (data_i1 | data_j1) & (data_k1 ^ data_l1);
    assign result_R = common_complex_sub + ((data_i2 | data_j2) & (data_k2 ^ data_l2));
    assign result_S = common_complex_sub - ((data_i2 | data_j2) & (data_k2 ^ data_l2));
endmodule
module sv_similar_struct_access_patterns (
    input logic [15:0] word_P, word_Q,
    output logic [7:0] field_sum_P, field_sum_Q, field_AND
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } byte_struct_t;
    byte_struct_t struct_P;
    byte_struct_t struct_Q;
    assign struct_P = word_P;
    assign struct_Q = word_Q;
    assign field_sum_P = struct_P.low + struct_P.high;
    assign field_sum_Q = struct_Q.low + struct_Q.high;
    assign field_AND = struct_P.low & struct_Q.low;
endmodule
module sv_similar_array_access_patterns (
    input logic [7:0] arr_one [0:3],
    input logic [7:0] arr_two [0:3],
    input logic [1:0] idx,
    output logic [15:0] indexed_product, 
    output logic [7:0] const_indexed_or
);
    assign indexed_product = $unsigned({8'b0, arr_one[idx]}) * $unsigned({8'b0, arr_two[idx]});
    assign const_indexed_or = arr_one[0] | arr_two[0];
endmodule
module sv_identical_case_branches (
    input logic [1:0] control_signal,
    input logic [7:0] input_val_A, input_val_B,
    output logic [7:0] case_output_val
);
    always_comb begin
        case (control_signal)
            2'b00: begin
                case_output_val = input_val_A + input_val_B;
            end
            2'b01: begin
                case_output_val = input_val_A - input_val_B;
            end
            2'b10: begin
                case_output_val = input_val_A ^ input_val_B;
            end
            2'b11: begin
                case_output_val = input_val_A ^ input_val_B;
            end
            default: case_output_val = 8'h5A;
        endcase
    end
endmodule
module sv_identical_if_bodies (
    input logic decision_flag,
    input logic [7:0] value_opt_X, value_opt_Y, modifier,
    output logic [7:0] if_statement_output
);
    always_comb begin
        if (decision_flag) begin
            if_statement_output = (value_opt_X & modifier) + 8'h10;
        end else begin
            if_statement_output = (value_opt_Y & modifier) + 8'h10;
        end
    end
endmodule
module sv_nested_struct_access (
    input logic [31:0] input_compound_word,
    output logic [7:0] nested_sum_result,
    output logic [7:0] nested_or_result
);
    typedef struct packed {
        logic [15:0] high_word;
        logic [15:0] low_word;
    } word_pair_t;
    typedef struct packed {
        logic [7:0] byte_lower;
        logic [7:0] byte_upper;
    } byte_pair_t;
    typedef struct packed {
        word_pair_t section1;
        byte_pair_t section2;
    } top_level_struct_t;
    top_level_struct_t composed_data;
    assign {composed_data.section1, composed_data.section2} = input_compound_word;
    assign nested_sum_result = composed_data.section1.high_word[7:0] + composed_data.section2.byte_lower;
    assign nested_or_result = composed_data.section1.low_word[15:8] | composed_data.section2.byte_upper;
endmodule
module sv_array_of_arrays_access (
    input logic [7:0] two_dim_array [0:1][0:1],
    input logic [0:0] row_index, col_index,
    output logic [7:0] indexed_access_or,
    output logic [7:0] diagonal_and
);
    assign indexed_access_or = two_dim_array[row_index][col_index] | two_dim_array[row_index][col_index];
    assign diagonal_and = two_dim_array[0][0] & two_dim_array[1][1];
endmodule
module sv_procedural_case_default (
    input logic [1:0] control_value,
    input logic [7:0] val0, val1, val2, val3,
    output logic [7:0] controlled_output
);
    always_comb begin
        case (control_value)
            2'b00: controlled_output = val0 & val1;
            2'b01: controlled_output = val0 | val1;
            2'b10: controlled_output = val2 + val3;
            default: controlled_output = val2 - val3;
        endcase
    end
endmodule

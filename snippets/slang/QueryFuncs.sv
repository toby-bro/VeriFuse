module BitsTypenameTest (
    input bit [7:0] in_packed,
    input int in_int,
    input real in_real,
    input logic [3:0][7:0] in_packed_array,
    input int in_unpacked_array_size_initial,
    output int out_bits_packed,
    output int out_bits_int,
    output int out_bits_real,
    output int out_bits_packed_array,
    output int out_bits_unpacked_array,
    output string out_typename_packed,
    output string out_typename_int,
    output string out_typename_real,
    output string out_typename_packed_array,
    output string out_typename_unpacked_array
);
    int dynamic_array [];
    initial begin
        if (in_unpacked_array_size_initial > 0) begin
            dynamic_array = new[in_unpacked_array_size_initial];
        end else begin
            dynamic_array = new[0];
        end
    end
    always_comb begin
        out_bits_packed = $bits(in_packed);
        out_bits_int = $bits(in_int);
        out_bits_real = $bits(in_real);
        out_bits_packed_array = $bits(in_packed_array);
        out_bits_unpacked_array = $bits(dynamic_array);
        out_typename_packed = $typename(in_packed);
        out_typename_int = $typename(in_int);
        out_typename_real = $typename(in_real);
        out_typename_packed_array = $typename(in_packed_array);
        out_typename_unpacked_array = $typename(dynamic_array);
    end
endmodule
module SimpleLogicTest (
    input bit [7:0] data_in,
    input bit select_signal,
    output bit [7:0] data_out
);
    logic [7:0] temp_data;
    always_comb begin
        if (select_signal) begin
            temp_data = data_in + 1;
        end else begin
            temp_data = data_in - 1;
        end
        data_out = temp_data;
    end
endmodule
module FixedArrayQueryTest (
    input bit [7:0] in_packed [4:1],
    input int in_unpacked_fixed [1:5],
    input string in_string,
    input int in_index,
    output int out_low_packed,
    output int out_high_packed,
    output int out_left_packed,
    output int out_right_packed,
    output int out_size_packed,
    output int out_increment_packed,
    output int out_low_unpacked_fixed,
    output int out_high_unpacked_fixed,
    output int out_left_unpacked_fixed,
    output int out_right_unpacked_fixed,
    output int out_size_unpacked_fixed,
    output int out_increment_unpacked_fixed,
    output int out_low_string,
    output int out_high_string,
    output int out_left_string,
    output int out_right_string,
    output int out_size_string,
    output int out_increment_string,
    output int out_low_packed_indexed,
    output int out_high_packed_indexed,
    output int out_left_packed_indexed,
    output int out_right_packed_indexed,
    output int out_size_packed_indexed,
    output int out_increment_packed_indexed,
    output int out_low_unpacked_fixed_indexed,
    output int out_high_unpacked_fixed_indexed,
    output int out_left_unpacked_fixed_indexed,
    output int out_right_unpacked_fixed_indexed,
    output int out_size_unpacked_fixed_indexed,
    output int out_increment_unpacked_fixed_indexed,
    output bit dummy_out
);
    bit dummy_wire_bool;
    int dummy_wire_int;
    always_comb begin
        out_low_packed = $low(in_packed);
        out_high_packed = $high(in_packed);
        out_left_packed = $left(in_packed);
        out_right_packed = $right(in_packed);
        out_size_packed = $size(in_packed);
        out_increment_packed = $increment(in_packed);
        out_low_unpacked_fixed = $low(in_unpacked_fixed);
        out_high_unpacked_fixed = $high(in_unpacked_fixed);
        out_left_unpacked_fixed = $left(in_unpacked_fixed);
        out_right_unpacked_fixed = $right(in_unpacked_fixed);
        out_size_unpacked_fixed = $size(in_unpacked_fixed);
        out_increment_unpacked_fixed = $increment(in_unpacked_fixed);
        out_low_string = $low(in_string);
        out_high_string = $high(in_string);
        out_left_string = $left(in_string);
        out_right_string = $right(in_string);
        out_size_string = $size(in_string);
        out_increment_string = $increment(in_string);
        out_low_packed_indexed = $low(in_packed, 1);
        out_high_packed_indexed = $high(in_packed, 1);
        out_left_packed_indexed = $left(in_packed, 1);
        out_right_packed_indexed = $right(in_packed, 1);
        out_size_packed_indexed = $size(in_packed, 1);
        out_increment_packed_indexed = $increment(in_packed, 1);
        out_low_unpacked_fixed_indexed = $low(in_unpacked_fixed, 1);
        out_high_unpacked_fixed_indexed = $high(in_unpacked_fixed, 1);
        out_left_unpacked_fixed_indexed = $left(in_unpacked_fixed, 1);
        out_right_unpacked_fixed_indexed = $right(in_unpacked_fixed, 1);
        out_size_unpacked_fixed_indexed = $size(in_unpacked_fixed, 1);
        out_increment_unpacked_fixed_indexed = $increment(in_unpacked_fixed, 1);
        dummy_wire_int = $low(in_packed, in_index);
        dummy_wire_int = $high(in_packed, in_index);
        dummy_wire_int = $left(in_packed, in_index);
        dummy_wire_int = $right(in_packed, in_index);
        dummy_wire_int = $size(in_packed, in_index);
        dummy_wire_int = $increment(in_packed, in_index);
        dummy_out = (dummy_wire_int == 0);
    end
endmodule
module DynamicArrayQueryTest (
    input int in_unpacked_dynamic_size_initial,
    input int in_index,
    output int out_low_dynamic,
    output int out_high_dynamic,
    output int out_left_dynamic,
    output int out_right_dynamic,
    output int out_size_dynamic,
    output int out_increment_dynamic,
    output int out_low_queue,
    output int out_high_queue,
    output int out_left_queue,
    output int out_right_queue,
    output int out_size_queue,
    output int out_increment_queue,
    output int out_low_dynamic_indexed,
    output bit dummy_out
);
    int dynamic_array [];
    int queue_array [$];
    int dummy_wire_int;
    initial begin
        if (in_unpacked_dynamic_size_initial > 0) begin
            dynamic_array = new[in_unpacked_dynamic_size_initial];
        end else begin
            dynamic_array = new[0];
        end
        queue_array.push_back(10);
        queue_array.push_back(20);
        queue_array.push_back(30);
    end
    always_comb begin
        out_low_dynamic = $low(dynamic_array);
        out_high_dynamic = $high(dynamic_array);
        out_left_dynamic = $left(dynamic_array);
        out_right_dynamic = $right(dynamic_array);
        out_size_dynamic = $size(dynamic_array);
        out_increment_dynamic = $increment(dynamic_array);
        out_low_queue = $low(queue_array);
        out_high_queue = $high(queue_array);
        out_left_queue = $left(queue_array);
        out_right_queue = $right(queue_array);
        out_size_queue = $size(queue_array);
        out_increment_queue = $increment(queue_array);
        out_low_dynamic_indexed = $low(dynamic_array, 1);
        dummy_out = (dummy_wire_int == 0);
    end
endmodule
module AssociativeArrayQueryTest (
    input int in_index_int,
    output int out_low_assoc_int_idx,
    output int out_high_assoc_int_idx,
    output int out_left_assoc_int_idx,
    output int out_right_assoc_int_idx,
    output int out_size_assoc_int_idx,
    output int out_increment_assoc_int_idx,
    output bit dummy_out
);
    int assoc_int [int];
    string assoc_str [string];
    int dummy_wire_int;
    initial begin
        assoc_int[5] = 100;
        assoc_int[1] = 200;
        assoc_int[10] = 300;
        assoc_str["apple"] = "1";
        assoc_str["banana"] = "2";
        assoc_str["cherry"] = "3";
    end
    always_comb begin
        out_low_assoc_int_idx = $low(assoc_int);
        out_high_assoc_int_idx = $high(assoc_int);
        out_left_assoc_int_idx = $left(assoc_int);
        out_right_assoc_int_idx = $right(assoc_int);
        out_size_assoc_int_idx = $size(assoc_int);
        out_increment_assoc_int_idx = $increment(assoc_int);
        dummy_wire_int = $low(assoc_int, 1);
        dummy_wire_int = $high(assoc_int, 1);
        dummy_wire_int = $left(assoc_int, 1);
        dummy_wire_int = $right(assoc_int, 1);
        dummy_wire_int = $size(assoc_int, 1);
        dummy_wire_int = $increment(assoc_int, 1);
        dummy_wire_int = $low(assoc_int, in_index_int);
        dummy_wire_int = $high(assoc_int, in_index_int);
        dummy_wire_int = $left(assoc_int, in_index_int);
        dummy_wire_int = $right(assoc_int, in_index_int);
        dummy_wire_int = $size(assoc_int, in_index_int);
        dummy_wire_int = $increment(assoc_int, in_index_int);
        dummy_out = (dummy_wire_int == 0);
    end
endmodule
module DimensionTest (
    input bit [7:0] in_packed,
    input bit [3:0][7:0] in_packed_multi,
    input int in_unpacked_fixed [1:5][6:10],
    input int in_unpacked_dynamic_size1_initial,
    input int in_unpacked_dynamic_size2_initial,
    output int out_dimensions_packed,
    output int out_dimensions_packed_multi,
    output int out_dimensions_unpacked_fixed_multi,
    output int out_dimensions_unpacked_dynamic,
    output int out_dimensions_unpacked_dynamic_multi,
    output int out_dimensions_unpacked_queue,
    output int out_dimensions_unpacked_associative,
    output int out_dimensions_string,
    output int out_dimensions_scalar,
    output int out_unpacked_dimensions_packed,
    output int out_unpacked_dimensions_packed_multi,
    output int out_unpacked_dimensions_unpacked_fixed_multi,
    output int out_unpacked_dimensions_unpacked_dynamic,
    output int out_unpacked_dimensions_unpacked_dynamic_multi,
    output int out_unpacked_dimensions_unpacked_queue,
    output int out_unpacked_dimensions_unpacked_associative,
    output int out_unpacked_dimensions_string,
    output int out_unpacked_dimensions_scalar,
    output bit dummy_out
);
    int dynamic_array [];
    int dynamic_array_multi [][];
    int queue_array [$];
    int assoc_array [int];
    string str_var = "test";
    int scalar_var = 42;
    initial begin
        if (in_unpacked_dynamic_size1_initial > 0) begin
            dynamic_array = new[in_unpacked_dynamic_size1_initial];
            dynamic_array_multi = new[in_unpacked_dynamic_size1_initial];
            if (in_unpacked_dynamic_size2_initial > 0) begin
                dynamic_array_multi[0] = new[in_unpacked_dynamic_size2_initial];
            end else begin
                 dynamic_array_multi[0] = new[0];
            end
        end else begin
            dynamic_array = new[0];
            dynamic_array_multi = new[0];
        end
        queue_array.push_back(1);
        assoc_array[5] = 1;
    end
    always_comb begin
        out_dimensions_packed = $dimensions(in_packed);
        out_dimensions_packed_multi = $dimensions(in_packed_multi);
        out_dimensions_unpacked_fixed_multi = $dimensions(in_unpacked_fixed);
        out_dimensions_unpacked_dynamic = $dimensions(dynamic_array);
        out_dimensions_unpacked_dynamic_multi = $dimensions(dynamic_array_multi);
        out_dimensions_unpacked_queue = $dimensions(queue_array);
        out_dimensions_unpacked_associative = $dimensions(assoc_array);
        out_dimensions_string = $dimensions(str_var);
        out_dimensions_scalar = $dimensions(scalar_var);
        out_unpacked_dimensions_packed = $unpacked_dimensions(in_packed);
        out_unpacked_dimensions_packed_multi = $unpacked_dimensions(in_packed_multi);
        out_unpacked_dimensions_unpacked_fixed_multi = $unpacked_dimensions(in_unpacked_fixed);
        out_unpacked_dimensions_unpacked_dynamic = $unpacked_dimensions(dynamic_array);
        out_unpacked_dimensions_unpacked_dynamic_multi = $unpacked_dimensions(dynamic_array_multi);
        out_unpacked_dimensions_unpacked_queue = $unpacked_dimensions(queue_array);
        out_unpacked_dimensions_unpacked_associative = $unpacked_dimensions(assoc_array);
        out_unpacked_dimensions_string = $unpacked_dimensions(str_var);
        out_unpacked_dimensions_scalar = $unpacked_dimensions(scalar_var);
        dummy_out = (out_dimensions_scalar == 1) && (out_unpacked_dimensions_scalar == 0);
    end
endmodule

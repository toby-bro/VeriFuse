module DynamicArrayQueryTest (
    input int in_index,
    input int in_unpacked_dynamic_size_initial,
    output bit dummy_out,
    output int out_high_dynamic,
    output int out_high_queue,
    output int out_increment_dynamic,
    output int out_increment_queue,
    output int out_left_dynamic,
    output int out_left_queue,
    output int out_low_dynamic,
    output int out_low_dynamic_indexed,
    output int out_low_queue,
    output int out_right_dynamic,
    output int out_right_queue,
    output int out_size_dynamic,
    output int out_size_queue
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


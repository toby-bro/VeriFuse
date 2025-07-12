module m_array_methods (
    input int init_val,
    input int unused_in,
    output int min_out,
    output int push_back_val,
    output int size_out,
    output int sum_out
);
    int my_queue [$];
    initial begin
        my_queue = '{1, 5, 2, 8, 3};
        size_out = my_queue.size();
        sum_out = my_queue.sum();
        if (my_queue.size() != 0) begin
            min_out = my_queue.min()[0];
        end else begin
            min_out = 0;
        end
        my_queue.sort();
        my_queue.push_back(init_val);
        push_back_val = my_queue[$];
    end
endmodule


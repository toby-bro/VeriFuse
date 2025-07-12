module module_foreach_dynamic_queue (
    input int in_size,
    input int in_value_offset,
    output int out_sum_dyn,
    output int out_sum_queue
);
    int dynamic_array[];
    int queue_var[$];
    int sum_dyn;
    int sum_queue;
    always_comb begin
        sum_dyn   = 0;
        sum_queue = 0;
        if (in_size > 0 && in_size < 10) begin
            dynamic_array = new[in_size];
            for (int i = 0; i < in_size; i++) begin
                dynamic_array[i] = i + in_value_offset;
            end
            foreach (dynamic_array[idx])
                sum_dyn = sum_dyn + dynamic_array[idx];
        end
        else
            dynamic_array = new[0];
        queue_var.delete();
        if (in_size > 0 && in_size < 10) begin
            for (int i = 0; i < in_size; i++) begin
                queue_var.push_back(i + in_value_offset + 10);
            end
            foreach (queue_var[idx])
                sum_queue = sum_queue + queue_var[idx];
        end
    end
    assign out_sum_dyn   = sum_dyn;
    assign out_sum_queue = sum_queue;
endmodule


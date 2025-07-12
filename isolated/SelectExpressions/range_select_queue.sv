module range_select_queue (
    input int end_index,
    input int in_val_push,
    input int start_index,
    output int out_slice_first,
    output int q_size
);
    int queue_var[$]; 
    always_comb begin
        int temp_q[$];
        if (in_val_push > 0) queue_var.push_back(in_val_push);
        q_size = queue_var.size(); 
        if (start_index >= 0 && end_index >= 0 && start_index <= end_index && end_index < q_size) begin
            for (int i = 0; i <= end_index-start_index; i++)
                temp_q.push_back(queue_var[start_index+i]);
            if (temp_q.size() > 0) out_slice_first = temp_q[0]; 
            else out_slice_first = 0;
        end else begin
            out_slice_first = 0; 
        end
    end
endmodule


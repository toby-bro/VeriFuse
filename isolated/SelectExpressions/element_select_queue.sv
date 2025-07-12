module element_select_queue (
    input int in_val_push,
    input int index_in,
    output int out_val,
    output int q_size
);
    int queue_var[$]; 
    always_comb begin
        if (in_val_push > 0) queue_var.push_back(in_val_push);
        q_size = queue_var.size(); 
        if (index_in >= 0 && index_in < q_size)
            out_val = queue_var[index_in];
        else
            out_val = 0; 
    end
endmodule


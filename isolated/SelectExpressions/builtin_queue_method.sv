module builtin_queue_method (
    input int in_val_push_b,
    input int in_val_push_f,
    input bit pop_en,
    output int out_delete_val,
    output int out_insert_val,
    output int out_val_pop,
    output int q_size
);
    int queue_var[$]; 
    always_comb begin
        if (in_val_push_b > 0) queue_var.push_back(in_val_push_b);
        if (in_val_push_f > 0) queue_var.push_front(in_val_push_f);
        if (queue_var.size() >= 2) queue_var.insert(1, 99);
        out_insert_val = (queue_var.size() >= 2 && queue_var[1] == 99) ? 99 : 0;
        if (queue_var.size() >= 3) queue_var.delete(2);
        if (pop_en && queue_var.size() > 0) begin
            out_val_pop = queue_var.pop_front();
        end else begin
            out_val_pop = 0;
        end
        q_size = queue_var.size(); 
    end
endmodule


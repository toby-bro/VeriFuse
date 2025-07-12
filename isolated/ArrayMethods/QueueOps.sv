module QueueOps (
    input int index_for_delete,
    input int index_for_insert,
    input int value_to_push,
    output int pop_back_val,
    output int pop_front_val,
    output int queue_delete_all_size,
    output int queue_size_after_delete_idx,
    output int queue_size_after_insert,
    output int queue_size_after_pop,
    output int queue_size_after_push
);
    int queue_arr_push[$];
    int queue_arr_pop[$];
    int queue_arr_insert[$];
    int queue_arr_delete_all[$];
    int queue_arr_delete_idx[$];
    int empty_queue[$];
    int temp_pop_front;
    int temp_pop_back;
    always_comb begin
        queue_arr_push = {1, 2};
        queue_arr_push.push_front(value_to_push);
        queue_arr_push.push_back(value_to_push + 1);
        queue_size_after_push = queue_arr_push.size();
        queue_arr_pop = {10, 20, 30};
        temp_pop_front = queue_arr_pop.pop_front();
        temp_pop_back = queue_arr_pop.pop_back();
        pop_front_val = temp_pop_front;
        pop_back_val = temp_pop_back;
        queue_size_after_pop = queue_arr_pop.size();
        queue_arr_insert = {100, 101, 102};
        queue_arr_insert.insert(index_for_insert, 999);
        queue_size_after_insert = queue_arr_insert.size();
        queue_arr_delete_all = {200, 201, 202, 203};
        queue_arr_delete_all.delete();
        queue_delete_all_size = queue_arr_delete_all.size();
        queue_arr_delete_idx = {300, 301, 302, 303, 304};
        queue_arr_delete_idx.delete(index_for_delete);
        queue_size_after_delete_idx = queue_arr_delete_idx.size();
        temp_pop_front = empty_queue.pop_front();
        empty_queue.delete();
        empty_queue.delete(0); 
    end
endmodule


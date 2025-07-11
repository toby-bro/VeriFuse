module ArrayReductionOps (
    input logic [7:0] in_val, 
    output logic [31:0] out_sum_fixed,
    output logic [31:0] out_sum_dynamic,
    output logic [31:0] out_sum_queue,
    output logic [31:0] out_sum_assoc,
    output logic [31:0] out_product_fixed,
    output logic [31:0] out_or_fixed,
    output logic [31:0] out_and_fixed,
    output logic [31:0] out_xor_fixed
);
    int fixed_arr[5];
    int dynamic_arr[];
    int queue_arr[$];
    int assoc_arr[string];
    always_comb begin
        fixed_arr = '{1, 2, 3, 4, 5};
        dynamic_arr = new[3]('{6, 7, 8});
        queue_arr = {9, 10, 11};
        assoc_arr.delete(); 
        assoc_arr["a"] = 12;
        assoc_arr["b"] = 13;
        out_sum_fixed = fixed_arr.sum();
        out_sum_dynamic = dynamic_arr.sum();
        out_sum_queue = queue_arr.sum();
        out_sum_assoc = assoc_arr.sum();
        out_product_fixed = fixed_arr.product();
        out_or_fixed = fixed_arr.or();
        out_and_fixed = fixed_arr.and();
        out_xor_fixed = fixed_arr.xor();
        dynamic_arr = new[0];
        queue_arr = {};
        assoc_arr.delete();
        out_sum_dynamic = dynamic_arr.sum(); 
        out_sum_queue = queue_arr.sum();     
        out_sum_assoc = assoc_arr.sum();     
    end
endmodule
module ArraySortReverseOps (
    input logic dummy_in, 
    output int sorted_fixed[5],
    output int rsorted_fixed[5],
    output int reversed_fixed[5],
    output int sorted_dynamic[],
    output int rsorted_dynamic[],
    output int reversed_dynamic[],
    output int sorted_queue[$],
    output int rsorted_queue[$],
    output int reversed_queue[$]
);
    int fixed_arr_sort[5];
    int fixed_arr_rsort[5];
    int fixed_arr_reverse[5];
    int dynamic_arr_sort[];
    int dynamic_arr_rsort[];
    int dynamic_arr_reverse[];
    int queue_arr_sort[$];
    int queue_arr_rsort[$];
    int queue_arr_reverse[$];
    always_comb begin
        fixed_arr_sort = '{5, 2, 8, 1, 9};
        fixed_arr_rsort = '{5, 2, 8, 1, 9};
        fixed_arr_reverse = '{5, 2, 8, 1, 9};
        dynamic_arr_sort = new[4]('{10, 6, 12, 7});
        dynamic_arr_rsort = new[4]('{10, 6, 12, 7});
        dynamic_arr_reverse = new[4]('{10, 6, 12, 7});
        queue_arr_sort = {15, 11, 18, 13};
        queue_arr_rsort = {15, 11, 18, 13};
        queue_arr_reverse = {15, 11, 18, 13};
        fixed_arr_sort.sort();
        fixed_arr_rsort.rsort();
        fixed_arr_reverse.reverse();
        dynamic_arr_sort.sort();
        dynamic_arr_rsort.rsort();
        dynamic_arr_reverse.reverse();
        queue_arr_sort.sort();
        queue_arr_rsort.rsort();
        queue_arr_reverse.reverse();
        sorted_fixed = fixed_arr_sort;
        rsorted_fixed = fixed_arr_rsort;
        reversed_fixed = fixed_arr_reverse;
        sorted_dynamic = dynamic_arr_sort;
        rsorted_dynamic = dynamic_arr_rsort;
        reversed_dynamic = dynamic_arr_reverse;
        sorted_queue = queue_arr_sort;
        rsorted_queue = queue_arr_rsort;
        reversed_queue = queue_arr_reverse;
        dynamic_arr_sort = new[0];
        dynamic_arr_rsort = new[0];
        dynamic_arr_reverse = new[0];
        queue_arr_sort = {};
        queue_arr_rsort = {};
        queue_arr_reverse = {};
        dynamic_arr_sort.sort();
        dynamic_arr_rsort.rsort();
        dynamic_arr_reverse.reverse();
        queue_arr_sort.sort();
        queue_arr_rsort.rsort();
        queue_arr_reverse.reverse();
        sorted_dynamic = dynamic_arr_sort; 
        rsorted_dynamic = dynamic_arr_rsort; 
        reversed_dynamic = dynamic_arr_reverse; 
        sorted_queue = queue_arr_sort; 
        rsorted_queue = queue_arr_rsort; 
        reversed_queue = queue_arr_reverse; 
    end
endmodule
module ArrayLocatorOps (
    input int threshold,
    output int find_q[$],
    output int find_index_q[$],
    output int find_first_q[$],
    output int find_first_index_q[$],
    output int find_last_q[$],
    output int find_last_index_q[$],
    output int find_assoc_q[$],
    output string find_index_assoc_q[$],
    output int find_first_assoc_q[$],
    output string find_first_index_assoc_q[$],
    output int find_last_assoc_q[$],
    output string find_last_index_assoc_q[$]
);
    int fixed_arr[5];
    int dynamic_arr[];
    int queue_arr[$];
    int assoc_arr[string];
    int empty_arr[];
    always_comb begin
        fixed_arr = '{10, 2, 30, 4, 50};
        dynamic_arr = new[6]('{1, 20, 3, 40, 5, 60});
        queue_arr = {7, 80, 9, 100};
        assoc_arr = '{"apple": 10, "banana": 20, "cherry": 10, "date": 30};
        empty_arr = new[0];
        find_q = fixed_arr.find() with (item > threshold);
        find_index_q = fixed_arr.find_index() with (item > threshold);
        find_first_q = fixed_arr.find_first() with (item > threshold);
        find_first_index_q = fixed_arr.find_first_index() with (item > threshold);
        find_last_q = fixed_arr.find_last() with (item > threshold);
        find_last_index_q = fixed_arr.find_last_index() with (item > threshold);
        find_q = dynamic_arr.find() with (item > threshold); 
        find_index_q = dynamic_arr.find_index() with (item > threshold);
        find_first_q = dynamic_arr.find_first() with (item > threshold);
        find_first_index_q = dynamic_arr.find_first_index() with (item > threshold);
        find_last_q = dynamic_arr.find_last() with (item > threshold);
        find_last_index_q = dynamic_arr.find_last_index() with (item > threshold);
        find_q = queue_arr.find() with (item > threshold); 
        find_index_q = queue_arr.find_index() with (item > threshold);
        find_first_q = queue_arr.find_first() with (item > threshold);
        find_first_index_q = queue_arr.find_first_index() with (item > threshold);
        find_last_q = queue_arr.find_last() with (item > threshold);
        find_last_index_q = queue_arr.find_last_index() with (item > threshold);
        find_assoc_q = assoc_arr.find() with (item > threshold);
        find_index_assoc_q = assoc_arr.find_index() with (item > threshold);
        find_first_assoc_q = assoc_arr.find_first() with (item > threshold);
        find_first_index_assoc_q = assoc_arr.find_first_index() with (item > threshold);
        find_last_assoc_q = assoc_arr.find_last() with (item > threshold);
        find_last_index_assoc_q = assoc_arr.find_last_index() with (item > threshold);
        find_q = empty_arr.find() with (item > threshold);
        find_index_q = empty_arr.find_index() with (item > threshold);
    end
endmodule
module ArrayMinMaxOps (
    input logic dummy_in, 
    output int min_fixed_q[$],
    output int max_fixed_q[$],
    output int min_dynamic_q[$],
    output int max_dynamic_q[$],
    output int min_queue_q[$],
    output int max_queue_q[$],
    output int min_assoc_q[$],
    output int max_assoc_q[$],
    output int min_fixed_with_q[$],
    output int max_fixed_with_q[$]
);
    int fixed_arr[5];
    int dynamic_arr[];
    int queue_arr[$];
    int assoc_arr[string];
    int empty_arr[];
    always_comb begin
        fixed_arr = '{10, 2, 8, 1, 9};
        dynamic_arr = new[4]('{5, 12, 6, 7});
        queue_arr = {20, 15, 25, 18};
        assoc_arr = '{"a": 10, "b": 5, "c": 15};
        empty_arr = new[0];
        min_fixed_q = fixed_arr.min();
        max_fixed_q = fixed_arr.max();
        min_dynamic_q = dynamic_arr.min();
        max_dynamic_q = dynamic_arr.max();
        min_queue_q = queue_arr.min();
        max_queue_q = queue_arr.max();
        min_assoc_q = assoc_arr.min();
        max_assoc_q = assoc_arr.max();
        min_fixed_with_q = fixed_arr.min() with (item + 1);
        max_fixed_with_q = fixed_arr.max() with (item + 1);
        min_dynamic_q = empty_arr.min(); 
        max_dynamic_q = empty_arr.max(); 
    end
endmodule
module ArrayUniqueOps (
    input logic dummy_in, 
    output int unique_fixed_q[$],
    output int unique_index_fixed_q[$],
    output int unique_dynamic_q[$],
    output int unique_index_dynamic_q[$],
    output int unique_queue_q[$],
    output int unique_index_queue_q[$],
    output int unique_assoc_q[$],
    output string unique_index_assoc_q[$],
    output int unique_fixed_with_q[$],
    output int unique_index_fixed_with_q[$]
);
    int fixed_arr[7];
    int dynamic_arr[];
    int queue_arr[$];
    int assoc_arr[string];
    int empty_arr[];
    always_comb begin
        fixed_arr = '{10, 2, 10, 4, 2, 50, 4};
        dynamic_arr = new[8]('{1, 20, 3, 1, 40, 5, 20, 3});
        queue_arr = {7, 80, 9, 7, 100, 80};
        assoc_arr = '{"a": 10, "b": 20, "c": 10, "d": 30, "e": 20};
        empty_arr = new[0];
        unique_fixed_q = fixed_arr.unique();
        unique_index_fixed_q = fixed_arr.unique_index();
        unique_dynamic_q = dynamic_arr.unique();
        unique_index_dynamic_q = dynamic_arr.unique_index();
        unique_queue_q = queue_arr.unique();
        unique_index_queue_q = queue_arr.unique_index();
        unique_assoc_q = assoc_arr.unique();
        unique_index_assoc_q = assoc_arr.unique_index();
        unique_fixed_with_q = fixed_arr.unique() with (item % 3);
        unique_index_fixed_with_q = fixed_arr.unique_index() with (item % 3);
        unique_dynamic_q = empty_arr.unique(); 
        unique_index_dynamic_q = empty_arr.unique_index(); 
    end
endmodule
module ArraySizeOps (
    input logic dummy_in, 
    output int dyn_size,
    output int queue_size,
    output int assoc_size,
    output int assoc_num
);
    int dynamic_arr[];
    int queue_arr[$];
    int assoc_arr[int];
    always_comb begin
        dynamic_arr = new[5];
        queue_arr = {1, 2, 3};
        assoc_arr[10] = 100;
        assoc_arr[20] = 200;
        dyn_size = dynamic_arr.size();
        queue_size = queue_arr.size();
        assoc_size = assoc_arr.size();
        assoc_num = assoc_arr.num();
        dynamic_arr = new[0];
        queue_arr = {};
        assoc_arr.delete();
        dyn_size = dynamic_arr.size();
        queue_size = queue_arr.size();
        assoc_size = assoc_arr.size();
        assoc_num = assoc_arr.num();
    end
endmodule
module DynamicArrayDeleteOp (
    input logic dummy_in, 
    output int dyn_array_size_before_delete,
    output int dyn_array_size_after_delete
);
    int dyn_arr[];
    always_comb begin
        dyn_arr = new[5]('{1, 2, 3, 4, 5});
        dyn_array_size_before_delete = dyn_arr.size();
        dyn_arr.delete();
        dyn_array_size_after_delete = dyn_arr.size();
    end
endmodule
module AssociativeArrayOps (
    input int key_to_check,
    output logic exists_result,
    output int assoc_array_size_after_delete1,
    output int assoc_array_size_after_delete2,
    output string first_key,
    output string last_key,
    output string next_key_out,
    output string prev_key_out,
    output logic next_key_valid, 
    output logic prev_key_valid
);
    int assoc_arr_exists[int];
    int assoc_arr_delete[string];
    int assoc_arr_traversal[string];
    string temp_first_key;
    string temp_last_key;
    string temp_next_key;
    string temp_prev_key;
    always_comb begin
        assoc_arr_exists.delete();
        assoc_arr_exists[10] = 100;
        assoc_arr_exists[20] = 200;
        exists_result = assoc_arr_exists.exists(key_to_check);
        assoc_arr_delete.delete();
        assoc_arr_delete["apple"] = 1;
        assoc_arr_delete["banana"] = 2;
        assoc_arr_delete["cherry"] = 3;
        assoc_arr_delete.delete("banana");
        assoc_array_size_after_delete1 = assoc_arr_delete.size();
        assoc_arr_delete.delete();
        assoc_array_size_after_delete2 = assoc_arr_delete.size();
        assoc_arr_traversal.delete();
        assoc_arr_traversal["z"] = 26;
        assoc_arr_traversal["a"] = 1;
        assoc_arr_traversal["m"] = 13;
        next_key_valid = assoc_arr_traversal.first(temp_first_key);
        prev_key_valid = assoc_arr_traversal.last(temp_last_key);
        temp_next_key = "a";
        temp_prev_key = "z";
        next_key_valid = assoc_arr_traversal.next(temp_next_key);
        prev_key_valid = assoc_arr_traversal.prev(temp_prev_key);
        first_key = next_key_valid ? temp_first_key : ""; 
        last_key = prev_key_valid ? temp_last_key : ""; 
        next_key_out = next_key_valid ? temp_next_key : "";
        prev_key_out = prev_key_valid ? temp_prev_key : "";
        assoc_arr_traversal.delete();
        next_key_valid = assoc_arr_traversal.first(temp_first_key); 
        prev_key_valid = assoc_arr_traversal.last(temp_last_key); 
    end
endmodule
module QueueOps (
    input int value_to_push,
    input int index_for_insert,
    input int index_for_delete,
    output int pop_front_val,
    output int pop_back_val,
    output int queue_size_after_push,
    output int queue_size_after_pop,
    output int queue_size_after_insert,
    output int queue_delete_all_size,
    output int queue_size_after_delete_idx
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

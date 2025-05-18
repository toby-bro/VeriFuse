module mod_begin_named (
    input logic in_a,
    input logic in_b,
    output logic out_result
);
    always_comb begin : logic_block
        logic temp;
        temp = in_a && in_b;
        out_result = temp;
    end
endmodule
module mod_nested_begins_if (
    input logic sel_outer,
    input logic sel_inner,
    output logic out_final
);
    always_comb begin : outer_scope
        logic inner_temp;
        if (sel_outer) begin : inner_if_scope
            inner_temp = sel_inner;
        end else begin : inner_else_scope
            inner_temp = 1'b0;
        end
        out_final = inner_temp;
    end
endmodule
module mod_fork_join_none (
    input logic start_op1,
    input logic start_op2,
    output logic done_op1,
    output logic done_op2
);
    always_comb begin
        fork
            begin
                done_op1 = start_op1;
            end
            begin
                done_op2 = start_op2;
            end
        join_none
    end
endmodule
module mod_foreach_array_internal (
    input int offset_val,
    input logic enable_op,
    output int array_sum_out
);
    int data_array[5] = {1, 2, 3, 4, 5};
    int sum;
    always_comb begin
        sum = 0;
        foreach (data_array[i]) begin
            if (enable_op) begin
                sum += data_array[i] + offset_val;
            end else begin
                sum += data_array[i];
            end
        end
        array_sum_out = sum;
    end
endmodule
module mod_foreach_queue_internal (
    input int multiplier,
    input logic apply_multiplier,
    output int queue_sum_out
);
    int my_queue[$] = {10, 20, 30};
    always_comb begin
        int sum = 0;
        foreach (my_queue[idx]) begin
            int item;
            item = my_queue[idx];
            if (apply_multiplier) begin
                sum += item * multiplier;
            end else begin
                sum += item;
            end
        end
        queue_sum_out = sum;
    end
endmodule
module mod_foreach_assoc_array_internal (
    input string search_key,
    input logic include_all,
    output int total_value
);
    int assoc_map[string] = '{"apple": 100, "banana": 200, "cherry": 300, "date": 400};
    always_comb begin : process_map
        int sum = 0;
        string key;
        total_value = 0;
        foreach (assoc_map[key]) begin
            if (include_all || key == search_key) begin
                sum += assoc_map[key];
            end
        end
        total_value = sum;
    end
endmodule
module mod_task_called_comb (
    input int val1,
    input int val2,
    output int result_sum
);
    task static calculate_sum_task;
        input int a;
        input int b;
        output int sum;
        int local_temp;
        local_temp = a + b;
        sum = local_temp;
    endtask
    always_comb begin
        int task_output;
        calculate_sum_task(val1, val2, task_output);
        result_sum = task_output;
    end
endmodule
module mod_typedef_example (
    input logic [15:0] raw_input,
    output logic [15:0] processed_output
);
    typedef logic [15:0] data_word_t;
    data_word_t internal_data;
    always_comb begin
        internal_data = raw_input;
        processed_output = internal_data;
    end
endmodule
module mod_typedef_in_begin (
    input logic [7:0] raw_byte,
    output logic [7:0] processed_byte
);
    always_comb begin : type_scope
        typedef logic [7:0] byte_t;
        byte_t internal_byte;
        internal_byte = raw_byte;
        processed_byte = internal_byte;
    end
endmodule
module mod_conditional_logic (
    input int score,
    input logic event_trigger,
    output logic is_score_high
);
    logic high_score_event;
    always_comb begin
        if (score > 90 && event_trigger) begin
            high_score_event = 1'b1;
        end else begin
            high_score_event = 1'b0;
        end
        is_score_high = high_score_event;
    end
endmodule
module mod_assignments (
    input int val1,
    input int val2,
    input logic select_assign,
    output int out_add,
    output int out_sel
);
    always_comb begin
        out_add = val1 + val2;
        if (select_assign) begin
            out_sel = val1;
        end else begin
            out_sel = val2;
        end
    end
endmodule
module mod_if_depth_check (
    input logic c1,
    input logic c2,
    input logic c3,
    input logic c4,
    input logic c5,
    output logic final_result
);
    always_comb begin
        if (c1) begin
            if (c2) begin
                if (c3) begin
                    if (c4) begin
                        if (c5) begin
                            final_result = 1'b1;
                        end else begin
                            final_result = 1'b0;
                        end
                    end else begin
                        final_result = 1'b0;
                    end
                end else begin
                    final_result = 1'b0;
                end
            end else begin
                final_result = 1'b0;
            end
        end else begin
            final_result = 1'b0;
        end
    end
endmodule
module mod_vars_in_begin (
    input int data_in,
    output int data_out_mult
);
    always_comb begin : data_process
        int temp1;
        int temp2;
        temp1 = data_in * 2;
        temp2 = temp1 + 5;
        data_out_mult = temp2;
    end
endmodule
module mod_coverage_example (
    input int data_value,
    input logic enable_check,
    output logic range_hit
);
    covergroup cg_data_value @(data_value or enable_check);
        coverpoint data_value {
            bins range1 = { [10:20] };
        }
    endgroup
    always_comb begin
        if (enable_check && data_value > 0) begin
            range_hit = 1'b1;
        end else begin
            range_hit = 1'b0;
        end
    end
endmodule

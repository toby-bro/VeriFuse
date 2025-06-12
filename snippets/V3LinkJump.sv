module module_return_task_automatic (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    task automatic my_task (input logic [7:0] value, output logic [7:0] result);
        logic [7:0] temp;
        temp = value + 1;
        if (temp > 10) begin
            result = 8'b0;
            return;
        end
        result = temp;
    endtask
    always_comb begin: task_call_block
        logic [7:0] task_result;
        my_task(in_data, task_result);
        out_data = task_result;
    end
endmodule
module module_return_func (
    input logic [7:0] in_val,
    output logic [7:0] out_res
);
    function automatic logic [7:0] my_func (input logic [7:0] value);
        logic [7:0] temp;
        temp = value * 2;
        if (temp > 50) begin
            return 8'hFF;
        end
        return temp;
    endfunction
    always_comb begin: func_call_block
        out_res = my_func(in_val);
    end
endmodule
module module_while_break (
    input logic [3:0] in_limit,
    output logic [3:0] out_count
);
    always_comb begin: while_block
        logic [3:0] i;
        out_count = 0;
        i = 0;
        while (i < 10) begin
            if (i >= in_limit) begin
                break;
            end
            out_count = out_count + 1;
            i = i + 1;
        end
    end
endmodule
module module_while_continue (
    input logic [3:0] in_skip,
    output logic [3:0] out_sum
);
    always_comb begin: while_cont_block
        logic [3:0] i;
        out_sum = 0;
        i = 0;
        while (i < 10) begin
            i = i + 1;
            if (i == in_skip) begin
                continue;
            end
            out_sum = out_sum + i;
        end
    end
endmodule
module module_for_break (
    input logic [3:0] in_target,
    output logic [3:0] out_idx
);
    always_comb begin: for_break_block
        out_idx = 0;
        for (int i = 0; i < 10; i++) begin
            out_idx = i;
            if (i == in_target) begin
                break;
            end
        end
    end
endmodule
module module_for_continue (
    input logic in_odd_only,
    output logic [3:0] out_accumulate
);
    always_comb begin: for_cont_block
        out_accumulate = 0;
        for (int i = 0; i < 10; i++) begin
            if (in_odd_only && (i % 2 == 0)) begin
                continue;
            end
            out_accumulate = out_accumulate + i;
        end
    end
endmodule
module module_repeat (
    input logic [3:0] in_times,
    output logic [3:0] out_counter
);
    always_comb begin: repeat_block
        logic [3:0] count_val;
        count_val = 0;
        repeat (in_times) begin
            count_val = count_val + 1;
        end
        out_counter = count_val;
    end
endmodule
module module_do_while (
    input logic [3:0] in_limit,
    output logic [3:0] out_value
);
    always_comb begin: do_while_block
        logic [3:0] i;
        logic [3:0] current_sum;
        current_sum = 0;
        i = 0;
        if (in_limit == 0) begin
            current_sum = 0; 
        end else begin
            i = 0;
            current_sum = 0;
            current_sum = current_sum + i;
            i = i + 1;
            while (i < in_limit) begin
                current_sum = current_sum + i;
                i = i + 1;
            end
        end
        out_value = current_sum;
    end
endmodule
module module_while_unroll_full_param (
    input logic dummy_in, 
    output logic [7:0] out_sum
);
    parameter PARAM_COUNT = 8;
    always_comb begin: while_unroll_block
        logic [3:0] i;
        out_sum = 0;
        i = 0;
        while (i < PARAM_COUNT) begin
            out_sum = out_sum + i;
            i = i + 1;
        end
    end
endmodule
module module_for_unroll_disable_input (
    input logic [3:0] in_limit,
    output logic [3:0] out_last_i
);
    always_comb begin: for_unroll_block
        out_last_i = 0;
        for (int i = 0; i < in_limit; i++) begin
            out_last_i = i;
        end
    end
endmodule
module module_nested_loops_break (
    input logic [1:0] in_outer_limit,
    input logic [1:0] in_inner_limit,
    output logic [3:0] out_value
);
    always_comb begin: nested_break_block
        logic [1:0] i, j;
        out_value = 0;
        i = 0;
        outer_loop: while (i < in_outer_limit) begin
            j = 0;
            inner_loop: while (j < in_inner_limit) begin
                if (i == 1 && j == 1) begin
                    break;
                end
                out_value = out_value + 1;
                j = j + 1;
            end
            i = i + 1;
        end
    end
endmodule
module module_nested_loops_continue (
    input logic [1:0] in_outer_limit,
    input logic [1:0] in_inner_limit,
    output logic [3:0] out_value
);
    always_comb begin: nested_cont_block
        logic [1:0] i, j;
        out_value = 0;
        i = 0;
        outer_loop: while (i < in_outer_limit) begin
            j = 0;
            inner_loop: while (j < in_inner_limit) begin
                j = j + 1;
                if (i == 1 && j == 1) begin
                    continue;
                end
                out_value = out_value + 1;
            end
            i = i + 1;
        end
    end
endmodule
module module_loop_idx_used (
    input logic [3:0] in_limit,
    output logic [7:0] out_sum_idx
);
    always_comb begin: loop_idx_block
        out_sum_idx = 0;
        for (int i = 0; i < in_limit; i = i + 1) begin
            out_sum_idx = out_sum_idx + i;
        end
    end
endmodule
module module_foreach (
    input logic [7:0] in_seed, 
    output logic [7:0] out_sum_array
);
    logic [3:0][7:0] internal_array; 
    always_comb begin: foreach_block
        for (int k = 0; k < 4; k++) begin
            internal_array[k] = in_seed + k;
        end
        out_sum_array = 0;
        foreach (internal_array[idx]) begin
            out_sum_array = out_sum_array + internal_array[idx];
        end
    end
endmodule
module module_foreach_break (
    input logic [7:0] in_seed, 
    input logic [7:0] in_stop,
    output logic [7:0] out_sum_partial
);
    logic [3:0][7:0] internal_array; 
    always_comb begin: foreach_break_block
        for (int k = 0; k < 4; k++) begin
            internal_array[k] = in_seed + k;
        end
        out_sum_partial = 0;
        foreach (internal_array[idx]) begin
            if (internal_array[idx] == in_stop) begin
                break;
            end
            out_sum_partial = out_sum_partial + internal_array[idx];
        end
    end
endmodule
module module_foreach_continue (
    input logic [7:0] in_seed, 
    input logic [7:0] in_skip,
    output logic [7:0] out_sum_filtered
);
    logic [3:0][7:0] internal_array; 
    always_comb begin: foreach_cont_block
        for (int k = 0; k < 4; k++) begin
            internal_array[k] = in_seed + k;
        end
        out_sum_filtered = 0;
        foreach (internal_array[idx]) begin
            if (internal_array[idx] == in_skip) begin
                continue;
            end
            out_sum_filtered = out_sum_filtered + internal_array[idx];
        end
    end
endmodule

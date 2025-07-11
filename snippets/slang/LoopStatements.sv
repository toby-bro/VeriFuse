module module_for_basic(
    input  logic [7:0] in_data,
    output logic [7:0] out_sum
);
    logic [7:0] sum_reg;
    always_comb begin
        sum_reg = 8'b0;
        for (int i = 0; i < in_data; i = i + 1) begin
            if (i == 4)
                continue;
            if (i == 8)
                break;
            sum_reg = sum_reg + i;
        end
    end
    assign out_sum = sum_reg;
endmodule
module module_while_do_while(
    input  logic [3:0] in_count,
    output logic [7:0] out_result
);
    logic [7:0] temp_res;
    logic [3:0] counter_w;
    logic [3:0] counter_dw;
    always_comb begin
        temp_res  = 8'b0;
        counter_w = in_count;
        while (counter_w > 0) begin
            temp_res = temp_res + 1;
            counter_w = counter_w - 1;
        end
        counter_dw = (in_count == 0) ? 1 : in_count;
        do begin
            temp_res = temp_res + 2;
            counter_dw = counter_dw - 1;
        end while (counter_dw > 0 && counter_dw < 10);
    end
    assign out_result = temp_res;
endmodule
module module_repeat_loop(
    input  logic [3:0] in_repeat_count,
    input  logic [7:0] in_add_val,
    output logic [15:0] out_total
);
    parameter int REPEAT_PARAM = 5;
    logic [15:0] total_sum;
    always_comb begin
        total_sum = 16'b0;
        repeat (REPEAT_PARAM) begin
            total_sum = total_sum + in_add_val;
        end
    end
    assign out_total = total_sum;
endmodule
module module_forever_loop(
    input  logic clk,
    input  logic reset_n,
    output logic toggle_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            toggle_out <= 1'b0;
        else
            forever begin
                toggle_out <= ~toggle_out;
                break;
            end
    end
endmodule
module module_foreach_fixed(
    input  logic [7:0] in_values [0:3],
    output logic [7:0] out_max
);
    logic [7:0] max_val;
    always_comb begin
        max_val = 8'b0;
        foreach (in_values[idx]) begin
            if (in_values[idx] > max_val)
                max_val = in_values[idx];
        end
    end
    assign out_max = max_val;
endmodule
module module_foreach_dynamic_queue(
    input  int in_size,
    input  int in_value_offset,
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
module module_foreach_associative_string(
    input  int  in_key1,
    input  int  in_val1,
    input  logic [7:0] in_char,
    output int  out_sum_assoc,
    output int  out_char_sum
);
    int    assoc_array[int];
    string my_string;
    int    sum_assoc;
    int    char_sum;
    always_comb begin
        sum_assoc = 0;
        char_sum  = 0;
        assoc_array.delete();
        assoc_array[in_key1] = in_val1;
        assoc_array[10]      = 200;
        assoc_array[3]       = -5;
        foreach (assoc_array[key])
            sum_assoc = sum_assoc + assoc_array[key];
        my_string = "abcdef";
        foreach (my_string[idx])
            char_sum = char_sum + my_string[idx];
        char_sum = char_sum + in_char;
    end
    assign out_sum_assoc = sum_assoc;
    assign out_char_sum  = char_sum;
endmodule
module module_foreach_multidim(
    input  logic [7:0] in_matrix [0:1][0:2],
    output logic [7:0] out_flat_sum,
    output logic [7:0] out_nested_sum
);
    logic [7:0] flat_sum;
    logic [7:0] nested_sum;
    always_comb begin
        flat_sum   = 8'b0;
        nested_sum = 8'b0;
        foreach (in_matrix[row, col])
            flat_sum = flat_sum + in_matrix[row][col];
        foreach (in_matrix[i])
            foreach (in_matrix[i][j])
                nested_sum = nested_sum + in_matrix[i][j];
    end
    assign out_flat_sum   = flat_sum;
    assign out_nested_sum = nested_sum;
endmodule
module module_subroutine_return(
    input  int in_a,
    input  int in_b,
    input  bit in_cond,
    output int out_add_result,
    output bit out_is_even
);
    function automatic int add_values(int val1, int val2);
        int temp = val1 + val2;
        if (temp > 100)
            return 100;
        return temp;
    endfunction
    task automatic check_even(input int value, output bit is_even);
        if ((value % 2) == 0) begin
            is_even = 1;
            return;
        end
        is_even = 0;
    endtask
    always_comb begin
        out_add_result = add_values(in_a, in_b);
        check_even(out_add_result, out_is_even);
    end
endmodule
module module_class_loop(
    input  int in_loop_count,
    input  int in_initial_val,
    output int out_class_sum
);
    class Adder;
        int value;
        function new(int initial_val);
            value = initial_val;
        endfunction
        function int add(int val);
            value += val;
            return value;
        endfunction
    endclass
    int total;
    always_comb begin
        Adder my_adder;
        total = 0;
        if (in_loop_count > 0 && in_loop_count < 10) begin
            my_adder = new(in_initial_val);
            for (int i = 0; i < in_loop_count; i++) begin
                total = my_adder.add(i);
            end
        end
        else
            total = in_initial_val;
    end
    assign out_class_sum = total;
endmodule
module module_complex_for(
    input  logic [7:0] in_start,
    input  logic [7:0] in_end,
    output logic [15:0] out_accum
);
    logic [15:0] accumulator;
    always_comb begin
        accumulator = 16'b0;
        for (int i = in_start, j = in_end; i < j; i = i + 1, j = j - 1) begin
            if (i < (j >> 1))
                accumulator = accumulator + i;
            else
                accumulator = accumulator - j;
            if ((i % 2) == 0)
                accumulator = accumulator + 1;
            else
                accumulator = accumulator - 1;
        end
    end
    assign out_accum = accumulator;
endmodule
module module_assignments_in_loops(
    input  logic [7:0] in_val,
    input  logic [2:0] in_shift,
    output logic [7:0] out_reg,
    output logic [3:0] out_part
);
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var;
    logic [3:0] part_var;
    always_comb begin
        reg_var  = in_val;
        part_var = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var  = reg_var + i;
            reg_var += (i * 2);
            reg_var <<= in_shift;
            reg_var[i % 8] = (reg_var[i % 8] == 1'b0);
            reg_var[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var = reg_var[7:4];
    end
    assign out_reg  = reg_var;
    assign out_part = part_var;
endmodule
module module_repeat_constant(
    input  logic [7:0] in_val,
    output logic [15:0] out_sum
);
    parameter int CONST_REPEAT = 7;
    logic [15:0] sum_val;
    always_comb begin
        sum_val = 16'b0;
        repeat (CONST_REPEAT)
            sum_val += in_val;
    end
    assign out_sum = sum_val;
endmodule
module module_nested_loop_jumps(
    input  logic [3:0] outer_limit,
    input  logic [3:0] inner_limit,
    output int out_count
);
    int count;
    always_comb begin
        count = 0;
        for (int i = 0; i < outer_limit; i++) begin
            for (int j = 0; j < inner_limit; j++) begin
                if (i == 1 && j == 1)
                    continue;
                if (i == 2 && j == 0)
                    break;
                if (i == 3 && j == 2)
                    break;
                count++;
            end
            if (i == 3)
                break;
        end
    end
    assign out_count = count;
endmodule
module module_foreach_nested_fixed_iter(
    input  logic [7:0] in_matrix [0:1][0:2],
    output logic [7:0] out_sum
);
    logic [7:0] total_sum;
    always_comb begin
        total_sum = 8'b0;
        foreach (in_matrix[row_idx])
            foreach (in_matrix[row_idx][col_idx])
                total_sum += in_matrix[row_idx][col_idx];
    end
    assign out_sum = total_sum;
endmodule
module module_foreach_nested_dynamic_queue_iter(
    input  int in_rows,
    input  int in_cols,
    output int out_nested_sum
);
    int dyn_2d[][];
    int queue_of_queues[$][$];
    int nested_sum;
    always_comb begin
        nested_sum = 0;
        if (in_rows > 0 && in_rows < 5 && in_cols > 0 && in_cols < 5) begin
            dyn_2d = new[in_rows];
            for (int i = 0; i < in_rows; i++) begin
                dyn_2d[i] = new[in_cols];
                for (int j = 0; j < in_cols; j++)
                    dyn_2d[i][j] = (i * 10) + j;
            end
            foreach (dyn_2d[row_idx])
                foreach (dyn_2d[row_idx][col_idx])
                    nested_sum += dyn_2d[row_idx][col_idx];
        end
        else
            dyn_2d = new[0];
        queue_of_queues.delete();
        if (in_rows > 0 && in_rows < 5 && in_cols > 0 && in_cols < 5) begin
            for (int i = 0; i < in_rows; i++) begin
                int inner_q[$];
                for (int j = 0; j < in_cols; j++)
                    inner_q.push_back((i * 100) + j);
                queue_of_queues.push_back(inner_q);
            end
            foreach (queue_of_queues[q_idx])
                foreach (queue_of_queues[q_idx][elem_idx])
                    nested_sum += queue_of_queues[q_idx][elem_idx];
        end
    end
    assign out_nested_sum = nested_sum;
endmodule
module module_loops_complex_cond(
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    input  logic [7:0] in_c,
    output logic [15:0] out_sum
);
    logic [15:0] result_sum;
    always_comb begin
        int i;
        int k;
        result_sum = 16'b0;
        i = 0;
        while ((i < in_a) && ((in_b > 10) || (in_c == 5))) begin
            result_sum += i;
            i++;
            if (i > 20)
                break;
        end
        for (int j = 0; (j < in_b) && ((in_a > 5) || (in_c != 10)); j++) begin
            result_sum += j * 2;
            if (j > 15)
                break;
        end
        k = 0;
        do begin
            result_sum += k * 3;
            k++;
            if (k > 12)
                break;
        end while ((k < in_c) && (in_a != in_b));
    end
    assign out_sum = result_sum;
endmodule

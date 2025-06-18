module stmt_while_task (
    input logic [7:0] data_in_m8,
    input logic [3:0] start_idx_m8,
    output logic [3:0] out_index_m8,
    output logic [7:0] out_sum_m8
);
    logic [3:0] index_var_m8;
    logic [7:0] sum_m8;
    logic [3:0] loop_limit_m8 = 5;
    task automatic process_while_m8(input logic [3:0] start_idx, input logic [7:0] data, output logic [7:0] total_sum, output logic [3:0] final_idx);
        logic [3:0] current_idx = start_idx;
        logic [7:0] current_sum = 0;
        logic [3:0] current_count = 0;
        while (current_count < loop_limit_m8) begin
            current_sum += data + current_idx;
            current_idx++;
            current_count++;
        end
        total_sum = current_sum;
        final_idx = current_idx;
    endtask
    always_comb begin
        process_while_m8(start_idx_m8, data_in_m8, sum_m8, index_var_m8);
        out_sum_m8 = sum_m8;
        out_index_m8 = index_var_m8;
    end
endmodule


module expr_preadd_comb (input logic [7:0] in_val_m1, input logic [7:0] add_val_m1, output logic [7:0] out_sum_m1, output logic [7:0] var_out_m1);
    logic [7:0] var_m1;
    always_comb begin
        var_m1 = in_val_m1;
        out_sum_m1 = (++var_m1) + add_val_m1;
        var_out_m1 = var_m1;
    end
endmodule
module expr_postsub_comb (input logic [7:0] in_val_m2, input logic [7:0] sub_val_m2, output logic [7:0] out_diff_m2, output logic [7:0] var_out_m2);
    logic [7:0] var_m2;
    always_comb begin
        var_m2 = in_val_m2;
        out_diff_m2 = (var_m2--) - sub_val_m2;
        var_out_m2 = var_m2;
    end
endmodule
module stmt_postadd_task (input logic [7:0] in_val_m3, output logic [7:0] var_out_m3);
    logic [7:0] var_m3;
    task automatic update_var_m3(inout logic [7:0] val);
        val++;
    endtask
    always_comb begin
        var_m3 = in_val_m3;
        update_var_m3(var_m3);
        var_out_m3 = var_m3;
    end
endmodule
module stmt_presub_task (input logic [7:0] in_val_m4, output logic [7:0] var_out_m4);
    logic [7:0] var_m4;
    task automatic update_var_m4(inout logic [7:0] val);
        --val;
    endtask
    always_comb begin
        var_m4 = in_val_m4;
        update_var_m4(var_m4);
        var_out_m4 = var_m4;
    end
endmodule
module stmt_array_sel_postadd_task (input logic [3:0] index_base_in_m5, input logic [7:0] data_init_in_m5, output logic [7:0] data_out_m5, output logic [3:0] se_var_out_m5);
    logic [7:0] byte_array_m5 [0:15];
    logic [3:0] index_side_effect_var_m5;
    function automatic logic [3:0] get_index_se_m5(input logic [3:0] base_idx, inout logic [3:0] se_counter);
        se_counter = se_counter + 1;
        return base_idx + se_counter[1:0];
    endfunction
    task automatic process_array_update_m5(input logic [3:0] index_base, inout logic [7:0] arr [0:15], inout logic [3:0] se_counter);
        arr [ get_index_se_m5(index_base, se_counter) ]++;
    endtask
    always_comb begin
        for (int i = 0; i < 16; i++) begin
            byte_array_m5[i] = data_init_in_m5;
        end
        index_side_effect_var_m5 = 0;
        process_array_update_m5(index_base_in_m5, byte_array_m5, index_side_effect_var_m5);
        se_var_out_m5 = index_side_effect_var_m5;
        data_out_m5 = byte_array_m5 [ index_base_in_m5 + index_side_effect_var_m5[1:0] ];
    end
endmodule
module stmt_if_task (input logic [7:0] in_val_m6, input bit condition_m6, output logic [7:0] out_val_m6);
    logic [7:0] var_m6;
    task automatic update_conditional_m6(input bit cond, inout logic [7:0] val);
        if (cond) begin
            val++;
        end else begin
            --val;
        end
    endtask
    always_comb begin
        var_m6 = in_val_m6;
        update_conditional_m6(condition_m6, var_m6);
        out_val_m6 = var_m6;
    end
endmodule
module stmt_case_task (input logic [1:0] selector_in_m7, input logic [7:0] data_in_m7, output logic [7:0] data_out_m7, output logic [1:0] selector_out_m7);
    logic [1:0] selector_var_m7;
    logic [7:0] result_m7;
    task automatic process_case_update_m7(input logic [1:0] selector, input logic [7:0] data, output logic [7:0] res, inout logic [1:0] sel_var);
        res = 0;
        case (selector)
            2'b00: begin
                res = data + 10;
                sel_var++;
            end
            2'b01: begin
                res = data + 20;
                sel_var--;
            end
            default: begin
                res = data;
            end
        endcase
    endtask
    always_comb begin
        selector_var_m7 = selector_in_m7;
        process_case_update_m7(selector_var_m7, data_in_m7, result_m7, selector_var_m7);
        data_out_m7 = result_m7;
        selector_out_m7 = selector_var_m7;
    end
endmodule
module stmt_while_task (input logic [3:0] start_idx_m8, input logic [7:0] data_in_m8, output logic [7:0] out_sum_m8, output logic [3:0] out_index_m8);
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
module unsupported_logand_expr (input logic [7:0] in_a_m9, input logic [7:0] in_b_m9, output logic out_m9);
    logic [7:0] var_m9;
    always_comb begin
        var_m9 = in_a_m9;
        if ((var_m9 > 10) && (in_b_m9 < 5)) begin
            out_m9 = 1;
        end else begin
            out_m9 = 0;
        end
        var_m9++;
    end
endmodule
module unsupported_cond_expr (input logic [7:0] in_val_m10, input bit condition_m10, output logic [7:0] out_val_m10);
    logic [7:0] var_m10;
    always_comb begin
        var_m10 = in_val_m10;
        out_val_m10 = condition_m10 ? var_m10 : var_m10;
        var_m10++;
    end
endmodule

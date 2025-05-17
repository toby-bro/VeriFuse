module ModuleIncExprAssign (
    input wire [7:0] a_in,
    input wire [7:0] b_in,
    input wire [7:0] c_in,
    input wire [7:0] d_in,
    input wire [7:0] e_in,
    input wire [7:0] f_in,
    input wire [7:0] g_in,
    output logic [7:0] out_pre_add_expr,
    output logic [7:0] out_post_sub_expr,
    output logic [7:0] out_pre_sub_expr,
    output logic [7:0] out_post_add_expr,
    output logic [7:0] a_out,
    output logic [7:0] d_out,
    output logic [7:0] e_out,
    output logic [7:0] g_out
);
    logic [7:0] val_a;
    logic [7:0] val_b;
    logic [7:0] val_c;
    logic [7:0] val_d;
    logic [7:0] val_e;
    logic [7:0] val_f;
    logic [7:0] val_g;
    always_comb begin
        val_a = a_in;
        val_b = b_in;
        out_pre_add_expr = (++val_a) + val_b;
        a_out = val_a;
        val_d = d_in;
        val_c = c_in;
        out_post_sub_expr = (val_d--) + val_c;
        d_out = val_d;
        val_e = e_in;
        val_f = f_in;
        out_pre_sub_expr = (--val_e) - val_f;
        e_out = val_e;
        val_g = g_in;
        out_post_add_expr = (val_g++) * 2;
        g_out = val_g;
    end
endmodule
module ModuleIncStmtStandalone (
    input wire [7:0] e_in,
    input wire [7:0] f_in,
    input wire [7:0] g_in,
    input wire [7:0] h_in,
    output logic [7:0] out_e_stmt,
    output logic [7:0] out_f_stmt,
    output logic [7:0] out_g_stmt,
    output logic [7:0] out_h_stmt
);
    logic [7:0] val_e;
    logic [7:0] val_f;
    logic [7:0] val_g;
    logic [7:0] val_h;
    always_comb begin
        val_e = e_in;
        val_f = f_in;
        val_g = g_in;
        val_h = h_in;
        ++val_e;
        val_f--;
        val_g++;
        --val_h;
        out_e_stmt = val_e;
        out_f_stmt = val_f;
        out_g_stmt = val_g;
        out_h_stmt = val_h;
    end
endmodule
module ModuleIncPackedArrayPureIdxStmt (
    input wire [1:0] idx_in_sel,
    input wire [7:0] array_in_sel [3:0],
    output logic [7:0] array_out_sel [3:0],
    output logic [1:0] idx_out_sel
);
    logic [1:0] idx_reg_sel;
    logic [7:0] array_reg_sel [3:0];
    always_comb begin
        array_reg_sel = array_in_sel;
        idx_reg_sel = idx_in_sel;
        ++array_reg_sel[idx_reg_sel];
        array_reg_sel[idx_reg_sel]--;
        array_reg_sel[idx_reg_sel]++;
        --array_reg_sel[idx_reg_sel];
        array_out_sel = array_reg_sel;
        idx_out_sel = idx_reg_sel;
    end
endmodule
module ModuleIncPackedArrayImpureIdxStmt (
    input wire [1:0] idx_in,
    input wire [7:0] array_in [3:0],
    output logic [7:0] array_out [3:0],
    output logic [1:0] idx_out
);
    logic [1:0] idx_reg;
    logic [7:0] array_reg [3:0];
    always_comb begin
        array_reg = array_in;
        idx_reg = idx_in;
        array_reg[idx_reg++]++;
        array_out = array_reg;
        idx_out = idx_reg;
    end
endmodule
module ModuleIncPackedArrayPureIdxExpr (
    input wire [1:0] idx_in,
    input wire [7:0] array_in [3:0],
    input wire [7:0] value_in,
    output logic [7:0] result_out_preadd,
    output logic [7:0] result_out_postsub,
    output logic [7:0] array_out [3:0]
);
    logic [1:0] idx_reg;
    logic [7:0] array_reg [3:0];
    always_comb begin
        idx_reg = idx_in;
        array_reg = array_in;
        result_out_preadd = (++array_reg[idx_reg]) + value_in;
        result_out_postsub = (array_reg[idx_reg]--) - value_in;
        array_out = array_reg;
    end
endmodule
module ModuleIncUnpackedArrayStmt (
    input wire [1:0] idx_un_in,
    input wire [7:0] array_un_in [4],
    output logic [7:0] array_un_out [4],
    output logic [1:0] idx_un_out
);
    logic [1:0] idx_un_reg;
    logic [7:0] array_un_reg [4];
    logic [1:0] pure_idx;
    always_comb begin
        array_un_reg = array_un_in;
        idx_un_reg = idx_un_in;
        pure_idx = idx_un_in;
        array_un_reg[pure_idx]++;
        ++array_un_reg[pure_idx];
        array_un_reg[pure_idx]--;
        --array_un_reg[pure_idx];
        array_un_out = array_un_reg;
        idx_un_out = idx_un_reg;
    end
endmodule
module ModuleIncUnpackedArrayImpureIdxStmt (
    input wire [1:0] idx_un_in,
    input wire [7:0] array_un_in [4],
    output logic [7:0] array_un_out [4],
    output logic [1:0] idx_un_out
);
    logic [1:0] idx_un_reg;
    logic [7:0] array_un_reg [4];
    always_comb begin
        array_un_reg = array_un_in;
        idx_un_reg = idx_un_in;
        array_un_reg[idx_un_reg++]++;
        array_un_out = array_un_reg;
        idx_un_out = idx_un_reg;
    end
endmodule
module ModuleIncIfElseStmt (
    input wire sel_in,
    input wire [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] data_reg;
    always_comb begin
        data_reg = data_in;
        if (sel_in) begin
            data_reg++;
        end else begin
            --data_reg;
        end
        data_out = data_reg;
    end
endmodule
module ModuleIncCaseStmt (
    input wire [1:0] sel_case,
    input wire [7:0] data_case_in,
    output logic [7:0] data_case_out
);
    logic [7:0] data_reg_case;
    always_comb begin
        data_reg_case = data_case_in;
        case (sel_case)
            2'b00: begin
                data_reg_case++;
            end
            2'b01: begin
                --data_reg_case;
            end
            default: begin
                data_reg_case = data_case_in;
            end
        endcase
        data_case_out = data_reg_case;
    end
endmodule
module ModuleIncWhileLoop (
    input wire [3:0] limit_in,
    input wire [3:0] start_idx_in,
    input wire [7:0] start_sum_in,
    output logic [3:0] final_idx_out,
    output logic [7:0] sum_out
);
    logic [3:0] idx;
    logic [7:0] sum;
    logic [3:0] limit;
    logic [3:0] idx_loop2;
    logic [7:0] sum_loop2;
    always_comb begin
        idx = start_idx_in;
        sum = start_sum_in;
        limit = limit_in;
        while (++idx < limit) begin
            sum = sum + 1;
        end
        idx_loop2 = start_idx_in;
        sum_loop2 = start_sum_in;
        while (idx_loop2 < limit_in) begin
             sum_loop2 = sum_loop2 + idx_loop2;
             idx_loop2++;
        end
        final_idx_out = idx_loop2;
        sum_out = sum_loop2;
    end
endmodule
module ModuleIncForeach (
    input wire [3:0] data_in [0:7],
    input wire [7:0] start_val_in,
    output logic [7:0] sum_out,
    output logic [7:0] last_counter_out,
    output logic [3:0] data_out_foreach [0:7]
);
    logic [7:0] sum;
    logic [3:0] temp_data [0:7];
    logic [7:0] counter;
    int j;
    always_comb begin
        sum = start_val_in;
        counter = 0;
        temp_data = data_in;
        foreach (temp_data[j]) begin
            sum = sum + temp_data[j];
        end
        foreach (temp_data[j]) begin
            counter++;
            sum = sum + counter;
        end
        last_counter_out = counter;
        foreach (temp_data[j]) begin
             if (temp_data[j] > 0)
                 temp_data[j]--;
        end
        sum_out = sum;
        data_out_foreach = temp_data;
    end
endmodule
module ModuleIncTaskCall (
    input wire [7:0] val_t_in,
    input wire [7:0] adjust_t_in,
    output logic [7:0] val_t_out
);
    logic [7:0] val_t_reg;
    task automatic adjust_value(input logic [7:0] adjust_by, inout logic [7:0] current_val);
        current_val++;
        --current_val;
        current_val = current_val - adjust_by;
        current_val = current_val + adjust_by;
    endtask
    always_comb begin
        val_t_reg = val_t_in;
        adjust_value(adjust_t_in, val_t_reg);
        val_t_out = val_t_reg;
    end
endmodule
module ModuleIncLogicalOpUnsupported (
    input wire [7:0] a_in,
    input wire [7:0] b_in,
    input wire [7:0] c_in,
    input wire [7:0] d_in,
    input wire [7:0] e_in,
    input wire [7:0] f_in,
    output logic out_and,
    output logic out_or,
    output logic out_eq,
    output logic [7:0] a_out_and,
    output logic [7:0] c_out_and,
    output logic [7:0] d_out_or,
    output logic [7:0] e_out_or,
    output logic [7:0] f_out_eq
);
    logic [7:0] reg_a_and, reg_c_and;
    logic [7:0] reg_d_or, reg_e_or;
    logic [7:0] reg_f_eq;
    always_comb begin
        reg_a_and = a_in;
        reg_c_and = c_in;
        reg_d_or = d_in;
        reg_e_or = e_in;
        reg_f_eq = f_in;
        out_and = (++reg_a_and > b_in) && (--reg_c_and < 10);
        a_out_and = reg_a_and;
        c_out_and = reg_c_and;
        out_or = (reg_d_or-- > b_in) || (reg_e_or++ < 20);
        d_out_or = reg_d_or;
        e_out_or = reg_e_or;
        out_eq = (++reg_f_eq == b_in);
        f_out_eq = reg_f_eq;
    end
endmodule
module ModuleIncTernaryOpUnsupported (
    input wire sel_in,
    input wire [7:0] val1_in,
    input wire [7:0] val2_in,
    output logic [7:0] result_out,
    output logic [7:0] val1_out,
    output logic [7:0] val2_out
);
    logic [7:0] val1_reg;
    logic [7:0] val2_reg;
    always_comb begin
        val1_reg = val1_in;
        val2_reg = val2_in;
        result_out = sel_in ? (++val1_reg) : (val2_reg--);
        val1_out = val1_reg;
        val2_out = val2_reg;
    end
endmodule
module ModuleIncEventControlStmt (
    input wire clk,
    input wire rst_n,
    input wire [7:0] data_in,
    input wire [3:0] counter_in,
    output logic [7:0] data_out,
    output logic [3:0] counter_out
);
    logic [7:0] data_reg;
    logic [3:0] counter_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_reg <= 0;
            counter_reg <= 0;
        end else begin
            counter_reg++;
            data_reg--;
        end
    end
    assign data_out = data_reg;
    assign counter_out = counter_reg;
endmodule
module ModuleIncJumpBlockStmt (
    input wire [3:0] limit_in,
    input wire [7:0] start_val_in,
    input wire [3:0] start_idx_in,
    output logic [7:0] final_val_out,
    output logic [3:0] final_idx_out
);
    logic [7:0] val_reg;
    logic [3:0] idx_reg;
    task automatic process_with_break(input logic [3:0] limit, inout logic [7:0] current_val, inout logic [3:0] current_idx);
        current_idx = start_idx_in;
        while (current_idx < 10) begin
            current_val++;
            if (current_idx == limit) begin
                break;
            end
            current_idx++;
        end
    endtask
    always_comb begin
        val_reg = start_val_in;
        idx_reg = 0;
        process_with_break(limit_in, val_reg, idx_reg);
        final_val_out = val_reg;
        final_idx_out = idx_reg;
    end
endmodule
module ModuleIncWaitStmt (
    input wire condition_in,
    input wire [7:0] data_in,
    output logic [7:0] data_out,
    output logic done_out
);
    logic [7:0] data_reg;
    logic done_reg;
    always @(condition_in, data_in) begin
        data_reg = data_in;
        done_reg = 1'b0;
        wait (condition_in);
        data_reg++;
        done_reg = 1'b1;
    end
    assign data_out = data_reg;
    assign done_out = done_reg;
endmodule
module ModuleIncLogicalIfUnsupported (
    input wire [7:0] a_in,
    input wire [7:0] b_in,
    output logic out_cond,
    output logic [7:0] a_out_cond
);
    logic [7:0] reg_a_cond;
    logic cond_reg;
    always_comb begin
        reg_a_cond = a_in;
        cond_reg = 1'b0;
        if (++reg_a_cond > b_in) begin
            cond_reg = 1'b1;
        end
        out_cond = cond_reg;
        a_out_cond = reg_a_cond;
    end
endmodule

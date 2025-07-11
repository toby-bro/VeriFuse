module split_basic_blocking (
    input logic [7:0] in1_a,
    output logic [7:0] out1_a
);
    always @(*) begin
        out1_a = in1_a;
    end
endmodule
module split_basic_nonblocking (
    input logic clk_b,
    input logic [7:0] in2_a,
    output logic [7:0] out2_a
);
    always @(posedge clk_b) begin
        out2_a <= in2_a;
    end
endmodule
module split_seq_dependency (
    input logic clk_c,
    input logic [7:0] in_val_c,
    output logic [7:0] out_val_c
);
    logic [7:0] mid_val_c;
    always @(posedge clk_c) begin
        mid_val_c <= in_val_c + 1;
        out_val_c <= mid_val_c * 2;
    end
endmodule
module split_conditional_nb (
    input logic clk_d,
    input logic condition_d,
    input logic [7:0] in_true_d,
    input logic [7:0] in_false_d,
    output logic [7:0] out_reg_d
);
    always @(posedge clk_d) begin
        if (condition_d) begin
            out_reg_d <= in_true_d;
        end else begin
            out_reg_d <= in_false_d;
        end
    end
endmodule
module split_mixed_cond_seq (
    input logic clk_e,
    input logic condition_e,
    input logic [7:0] in_val_e,
    input logic [7:0] in_override_e,
    output logic [7:0] out_val_e,
    output logic status_e
);
    logic [7:0] temp_val_e;
    always @(posedge clk_e) begin
        temp_val_e <= in_val_e + 5;
        if (condition_e) begin
            out_val_e <= temp_val_e;
            status_e <= 1;
        end else begin
            out_val_e <= in_override_e;
            status_e <= 0;
        end
    end
endmodule
module split_independent_nb (
    input logic clk_f,
    input logic [7:0] in1_f,
    input logic [7:0] in2_f,
    input logic [7:0] in3_f,
    output logic [7:0] out1_f,
    output logic [7:0] out2_f,
    output logic [7:0] out3_f
);
    always @(posedge clk_f) begin
        out1_f <= in1_f;
        out2_f <= in2_f;
        out3_f <= in3_f;
    end
endmodule
module split_reorder_blocking (
    input logic [7:0] in_a_g,
    input logic [7:0] in_b_g,
    output logic [7:0] out_p_g,
    output logic [7:0] out_q_g
);
    logic [7:0] mid_x_g;
    logic [7:0] mid_y_g;
    always @(*) begin
        mid_x_g = in_a_g * 2;
        mid_y_g = mid_x_g + in_b_g;
        out_p_g = mid_y_g - 1;
        out_q_g = mid_x_g / 2;
    end
endmodule
module split_if_only_then (
    input logic clk_h,
    input logic condition_h,
    input logic [7:0] in_val_h,
    output logic [7:0] out_reg_h
);
    always @(posedge clk_h) begin
        if (condition_h) begin
            out_reg_h <= in_val_h;
        end
    end
endmodule
module split_for_loop (
    input logic clk_i,
    input logic [7:0] start_val_i,
    output logic [15:0] sum_out_i
);
    always @(posedge clk_i) begin
        sum_out_i <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            sum_out_i <= sum_out_i + start_val_i + i;
        end
    end
endmodule
module split_multiple_in_branch (
    input logic clk_j,
    input logic condition_j,
    input logic [7:0] in_a_j,
    input logic [7:0] in_b_j,
    output logic [7:0] out_x_j,
    output logic [7:0] out_y_j
);
    always @(posedge clk_j) begin
        if (condition_j) begin
            out_x_j <= in_a_j * 3;
            out_y_j <= in_b_j + 1;
        end else begin
            out_x_j <= in_a_j;
            out_y_j <= in_b_j;
        end
    end
endmodule
module split_input_only_var (
    input logic clk_k,
    input logic control_signal_k,
    input logic [7:0] data_in_k,
    output logic [7:0] data_out_k
);
    always @(posedge clk_k) begin
        if (control_signal_k) begin
            data_out_k <= data_in_k;
        end
    end
endmodule
module split_inputs_outputs_only (
    input logic [7:0] in_val_a_l,
    input logic [7:0] in_val_b_l,
    output logic [8:0] out_val_c_l,
    output logic [7:0] out_val_d_l
);
    always @(*) begin
        out_val_c_l = in_val_a_l + in_val_b_l;
        out_val_d_l = in_val_a_l - in_val_b_l;
    end
endmodule
module split_nested_if (
    input logic clk_m,
    input logic cond1_m,
    input logic cond2_m,
    input logic [7:0] val_a_m,
    input logic [7:0] val_b_m,
    input logic [7:0] val_c_m,
    output logic [7:0] result_m
);
    always @(posedge clk_m) begin
        if (cond1_m) begin
            if (cond2_m) begin
                result_m <= val_a_m;
            end else begin
                result_m <= val_b_m;
            end
        end else begin
            result_m <= val_c_m;
        end
    end
endmodule
module split_multiple_blocking (
    input logic [3:0] data_in_n,
    output logic [3:0] data_out1_n,
    output logic [3:0] data_out2_n
);
    logic [3:0] temp_n;
    always @(*) begin
        temp_n = data_in_n + 1;
        data_out1_n = temp_n * 2;
        data_out2_n = temp_n + 3;
    end
endmodule
module split_conditional_blocking (
    input logic condition_o,
    input logic [7:0] in_true_o,
    input logic [7:0] in_false_o,
    output logic [7:0] out_val_o
);
    always @(*) begin
        if (condition_o) begin
            out_val_o = in_true_o;
        end else begin
            out_val_o = in_false_o;
        end
    end
endmodule
module split_if_empty_then (
    input logic clk_p,
    input logic condition_p,
    input logic [7:0] in_val_p,
    output logic [7:0] out_reg_p
);
    always @(posedge clk_p) begin
        if (condition_p) begin
        end else begin
            out_reg_p <= in_val_p;
        end
    end
endmodule
module split_single_stmt (
    input logic [7:0] in_q,
    output logic [7:0] out_q
);
    always @(*) begin
        out_q = in_q + 1;
    end
endmodule
module split_complex_blocking (
    input logic [7:0] i1_r, i2_r, i3_r,
    output logic [7:0] o1_r, o2_r, o3_r
);
    logic [7:0] t1_r, t2_r;
    always @(*) begin
        t1_r = i1_r + i2_r;
        o1_r = t1_r - i3_r;
        t2_r = i2_r * i3_r;
        o2_r = t1_r + t2_r;
        o3_r = t2_r / 2;
    end
endmodule
module split_complex_nb (
    input logic clk_s,
    input logic [7:0] i1_s, i2_s, i3_s,
    output logic [7:0] o1_s, o2_s, o3_s
);
    logic [7:0] t1_s, t2_s;
    always @(posedge clk_s) begin
        t1_s <= i1_s + i2_s;
        o1_s <= t1_s - i3_s;
        t2_s <= i2_s * i3_s;
        o2_s <= t1_s + t2_s;
        o3_s <= t2_s / 2;
    end
endmodule
module split_if_empty_branches (
    input logic clk_t,
    input logic condition_t,
    input logic [7:0] in_val_t,
    output logic [7:0] out_reg_t
);
    always @(posedge clk_t) begin
        if (condition_t) begin
        end else begin
        end
    end
endmodule
module split_arith_blocking (
    input logic [7:0] op1_u, op2_u,
    output logic [7:0] sum_u, diff_u, prod_u
);
    always @(*) begin
        sum_u = op1_u + op2_u;
        diff_u = op1_u - op2_u;
        prod_u = op1_u * op2_u;
    end
endmodule
module split_arith_nb (
    input logic clk_v,
    input logic [7:0] op1_v, op2_v,
    output logic [7:0] sum_v, diff_v, prod_v
);
    always @(posedge clk_v) begin
        sum_v <= op1_v + op2_v;
        diff_v <= op1_v - op2_v;
        prod_v <= op1_v * op2_v;
    end
endmodule
module split_case (
    input logic clk_w,
    input logic [1:0] sel_w,
    input logic [7:0] d0_w, d1_w, d2_w, d3_w,
    output logic [7:0] out_w
);
    always @(posedge clk_w) begin
        case (sel_w)
            2'b00: out_w <= d0_w;
            2'b01: out_w <= d1_w;
            2'b10: out_w <= d2_w;
            default: out_w <= d3_w;
        endcase
    end
endmodule
module split_ifelse_chain (
    input logic clk_x,
    input logic c1_x, c2_x, c3_x,
    input logic [7:0] v1_x, v2_x, v3_x, v4_x,
    output logic [7:0] out_x
);
    always @(posedge clk_x) begin
        if (c1_x) begin
            out_x <= v1_x;
        end else if (c2_x) begin
            out_x <= v2_x;
        end else if (c3_x) begin
            out_x <= v3_x;
        end else begin
            out_x <= v4_x;
        end
    end
endmodule
module split_vector_assign (
    input logic clk_y,
    input logic condition_y,
    input logic [7:0] in_val_y,
    output logic [7:0] out_vec_y
);
    always @(posedge clk_y) begin
        if (condition_y) begin
            out_vec_y[3:0] <= in_val_y[3:0];
            out_vec_y[7:4] <= in_val_y[7:4] + 1;
        end else begin
            out_vec_y <= 8'hFF;
        end
    end
endmodule
module split_diff_vars_branches (
    input logic clk_z,
    input logic condition_z,
    input logic [7:0] in1_z, in2_z,
    output logic [7:0] out1_z, out2_z
);
    always @(posedge clk_z) begin
        if (condition_z) begin
            out1_z <= in1_z;
        end else begin
            out2_z <= in2_z;
        end
    end
endmodule
module split_combo_blocking (
    input logic [7:0] a_aa, b_aa, c_aa,
    output logic [7:0] x_aa, y_aa, z_aa
);
    logic [7:0] temp_aa;
    always @(*) begin
        x_aa = a_aa + b_aa;
        y_aa = x_aa - c_aa;
        z_aa = a_aa * c_aa;
    end
endmodule
module split_combo_nb (
    input logic clk_bb,
    input logic [7:0] a_bb, b_bb, c_bb,
    output logic [7:0] x_bb, y_bb, z_bb
);
    logic [7:0] temp_bb;
    always @(posedge clk_bb) begin
        x_bb <= a_bb + b_bb;
        y_bb <= x_bb - c_bb;
        z_bb <= a_bb * c_bb;
    end
endmodule
module split_conditional_reorder (
    input logic clk_cc,
    input logic condition_cc,
    input logic [7:0] val1_cc, val2_cc, val3_cc,
    output logic [7:0] out_reg_cc
);
    always @(posedge clk_cc) begin
        out_reg_cc <= val1_cc;
        if (condition_cc) begin
            out_reg_cc <= val2_cc;
        end else begin
            out_reg_cc <= val3_cc;
        end
    end
endmodule
module split_multi_nb_in_if (
    input logic clk_dd,
    input logic cond_dd,
    input logic [7:0] in1_dd, in2_dd, in3_dd, in4_dd,
    output logic [7:0] out1_dd, out2_dd
);
    always @(posedge clk_dd) begin
        if (cond_dd) begin
            out1_dd <= in1_dd + in2_dd;
            out2_dd <= in3_dd - in4_dd;
        end else begin
            out1_dd <= in1_dd * in2_dd;
            out2_dd <= in3_dd / (in4_dd + 1);
        end
    end
endmodule

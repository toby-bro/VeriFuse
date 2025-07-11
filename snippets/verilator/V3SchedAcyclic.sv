module simple_loop (
    input logic i_a,
    input logic i_en,
    output logic o_z
);
    logic r_b;
    logic r_c;
    always_comb begin
        r_b = r_c ^ i_a;
        r_c = r_b & i_en;
        o_z = r_c | i_a;
    end
endmodule
module wide_loop (
    input logic [15:0] i_data,
    input logic       i_control,
    output logic [15:0] o_result
);
    logic [15:0] r_temp1;
    logic [15:0] r_temp2;
    always_comb begin
        r_temp1 = r_temp2 + i_data;
        r_temp2 = r_temp1 ^ {16{i_control}};
        o_result = r_temp1 & r_temp2;
    end
endmodule
module multi_var_loop (
    input logic       i_p,
    input logic       i_q,
    input logic       i_r_in,
    output logic      o_x,
    output logic      o_y,
    output logic      o_z
);
    logic r_v, r_w, r_z;
    always_comb begin
        r_v = r_z | i_p;
        r_w = r_v & i_q;
        r_z = r_w ^ i_r_in;
        o_x = r_v;
        o_y = r_w;
        o_z = r_z;
    end
endmodule
module named_block_logic (
    input logic i_in,
    input logic i_gate,
    output logic o_out
);
    logic r_internal;
    logic r_temp;
    always_comb begin : my_combinational_block
        r_temp = i_in & i_gate;
        r_internal = r_temp;
        o_out = r_internal;
    end
endmodule
module split_var_candidate (
    input logic [63:0] i_large_data_a,
    input logic [63:0] i_large_data_b,
    output logic [63:0] o_sum,
    output logic [63:0] o_feedback
);
    logic [63:0] r_feedback_reg;
    logic [63:0] r_intermediate;
    always_comb begin
        r_intermediate = i_large_data_a + r_feedback_reg;
        r_feedback_reg = r_intermediate ^ i_large_data_b;
        o_sum = r_intermediate;
        o_feedback = r_feedback_reg;
    end
endmodule
module another_loop (
    input logic i_i1,
    input logic i_i2,
    input logic i_i3,
    output logic o_o1,
    output logic o_o2
);
    logic r_s1, r_s2, r_s3;
    always_comb begin
        r_s1 = r_s3 | i_i1;
        r_s2 = r_s1 & i_i2;
        r_s3 = r_s2 ^ i_i3;
        o_o1 = r_s1 & r_s2;
        o_o2 = r_s3;
    end
endmodule
module vector_loop (
    input logic [7:0] i_vec_in,
    input logic [7:0] i_vec_control,
    output logic [7:0] o_vec_out
);
    logic [7:0] r_vec_feedback;
    logic [7:0] r_vec_temp;
    always_comb begin
        r_vec_temp[3:0] = r_vec_feedback[3:0] ^ i_vec_in[3:0];
        r_vec_temp[7:4] = r_vec_feedback[7:4] | i_vec_in[7:4];
        r_vec_feedback = {r_vec_temp[7:4], r_vec_temp[3:0]};
        o_vec_out = r_vec_temp;
    end
endmodule
module explicit_assign_loop (
    input logic i_sig_a,
    input logic i_sig_b,
    input logic i_sig_c,
    output logic o_sig_x
);
    logic r_inter_p;
    logic r_inter_q;
    always_comb begin
        r_inter_p = r_inter_q | i_sig_a;
        r_inter_q = r_inter_p & i_sig_b;
        o_sig_x = r_inter_p ^ i_sig_c;
    end
endmodule

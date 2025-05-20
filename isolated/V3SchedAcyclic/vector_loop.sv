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


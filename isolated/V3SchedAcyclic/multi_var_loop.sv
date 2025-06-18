module multi_var_loop (
    input logic i_p,
    input logic i_q,
    input logic i_r_in,
    output logic o_x,
    output logic o_y,
    output logic o_z
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


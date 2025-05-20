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


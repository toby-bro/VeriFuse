module UnaryOps (
    input int in_int,
    input real in_real,
    input logic [7:0] in_vec,
    output logic [7:0] out_bit_not,
    output logic out_log_not,
    output int out_minus,
    output logic [7:0] out_plus,
    output int out_postdec,
    output int out_preinc,
    output real out_real_postinc,
    output real out_real_predec,
    output logic out_red_and
);
    int  l_int;
    real l_real;
    always_comb begin
        out_plus         = +in_vec;
        out_minus        = -in_int;
        out_log_not      = !in_vec[0];
        out_bit_not      = ~in_vec;
        out_red_and      = &in_vec;
        l_int            = in_int;
        l_real           = in_real;
        out_preinc       = ++l_int;
        out_postdec      = l_int--;
        out_real_predec  = --l_real;
        out_real_postinc = l_real++;
    end
endmodule


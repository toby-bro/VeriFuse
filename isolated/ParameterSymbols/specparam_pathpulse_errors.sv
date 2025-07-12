module specparam_pathpulse_errors (
    input wire i_term_in,
    output logic o_term_out
);
    logic internal_sig;
    specify
        (i_term_in => o_term_out) = (20ps, 20ps);
    endspecify
    always_comb begin
        o_term_out = i_term_in;
        internal_sig = i_term_in | o_term_out;
    end
endmodule


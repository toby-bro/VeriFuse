module specify_basic (
    input wire in_sig,
    output wire out_sig
);
    specparam delay_val = 2;
    specify
        (in_sig => out_sig) = delay_val;
    endspecify
endmodule


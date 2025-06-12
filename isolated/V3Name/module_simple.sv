module module_simple (
    input wire i_a,
    input wire i_b,
    output wire o_c
);
    wire internal_xor_res;
    assign internal_xor_res = i_a ^ i_b;
    assign o_c = internal_xor_res & i_a;
endmodule


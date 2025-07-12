module primitive_example (
    input logic i_p1,
    input logic i_p2,
    output logic o_p_and,
    output logic o_p_xor
);
    and (o_p_and, i_p1, i_p2);
    xor (o_p_xor, i_p1, i_p2);
endmodule


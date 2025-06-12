module LogicTri (
    output wire or_out,
    output wire and_out,
    input wire a_in,
    input wire b_en
);
    wire b_tri;
    assign b_tri = b_en ? 1'b1 : 1'bz;
    assign or_out = a_in | b_tri;
    assign and_out = a_in & b_tri;
endmodule


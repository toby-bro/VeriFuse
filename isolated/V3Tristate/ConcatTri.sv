module ConcatTri (
    input wire [2:0] b,
    input wire c_en,
    output wire [4:0] out_concat,
    input wire a
);
    wire c_tri;
    assign c_tri = c_en ? 1'b1 : 1'bz;
    assign out_concat = {a, b, c_tri};
endmodule


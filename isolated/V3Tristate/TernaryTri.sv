module TernaryTri (
    input wire data_else_en,
    input wire data_then,
    input wire sel_cond,
    output wire out_ternary
);
    wire data_else_tri;
    assign data_else_tri = data_else_en ? 1'b0 : 1'bz;
    assign out_ternary = sel_cond ? data_then : data_else_tri;
endmodule


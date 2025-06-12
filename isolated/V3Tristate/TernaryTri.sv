module TernaryTri (
    input wire data_then,
    input wire data_else_en,
    output wire out_ternary,
    input wire sel_cond
);
    wire data_else_tri;
    assign data_else_tri = data_else_en ? 1'b0 : 1'bz;
    assign out_ternary = sel_cond ? data_then : data_else_tri;
endmodule


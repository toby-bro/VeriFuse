module TristateBasic (
    input wire data,
    input wire en,
    output wire out,
    inout wire tri_io
);
    assign tri_io = en ? data : 1'bz;
    assign out = tri_io;
endmodule


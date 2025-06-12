module TristateBasic (
    inout wire tri_io,
    output wire out,
    input wire en,
    input wire data
);
    assign tri_io = en ? data : 1'bz;
    assign out = tri_io;
endmodule


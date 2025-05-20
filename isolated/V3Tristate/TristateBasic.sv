module TristateBasic (
    input wire en,
    input wire data,
    inout wire tri_io,
    output wire out
);
    assign tri_io = en ? data : 1'bz;
    assign out = tri_io;
endmodule


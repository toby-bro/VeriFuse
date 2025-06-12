module SelectSlice (
    output wire out_bit,
    input wire [7:0] data_in,
    input wire sel_en,
    output wire [3:0] out_slice
);
    wire [7:0] tri_bus;
    assign tri_bus = sel_en ? data_in : 8'bz;
    assign out_slice = tri_bus[3:0];
    assign out_bit = tri_bus[7];
endmodule


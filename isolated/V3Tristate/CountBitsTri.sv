module CountBitsTri (
    input wire en_tri,
    output wire [3:0] count_ones,
    output wire [3:0] count_z_ph,
    output wire [3:0] count_0s_ph,
    input wire [7:0] data_in
);
    wire [7:0] tri_data;
    assign tri_data = en_tri ? 8'b1011_z00z : data_in;
    assign count_ones = $countones(tri_data);
    assign count_z_ph = 4'b0000;
    assign count_0s_ph = tri_data[3:0];
endmodule


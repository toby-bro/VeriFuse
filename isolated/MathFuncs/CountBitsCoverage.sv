module CountBitsCoverage (
    input logic [7:0] vector_in,
    output int countbits_01_out,
    output int countbits_01xz_out,
    output int countbits_0_out,
    output int countbits_1_out,
    output int countbits_x_out,
    output int countbits_z_out
);
always @(*) begin
    countbits_0_out = $countbits(vector_in, 1'b0);
    countbits_1_out = $countbits(vector_in, 1'b1);
    countbits_x_out = $countbits(vector_in, 1'bx);
    countbits_z_out = $countbits(vector_in, 1'bz);
    countbits_01_out = $countbits(vector_in, 1'b0, 1'b1);
    countbits_01xz_out = $countbits(vector_in, 1'b0, 1'b1, 1'bx, 1'bz);
end
endmodule


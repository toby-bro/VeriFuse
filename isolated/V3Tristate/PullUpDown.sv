module PullUpDown (
    input wire data_in,
    output wire out_pull,
    inout wire tri_pulled
);
    pullup (tri_pulled);
    assign out_pull = tri_pulled;
endmodule


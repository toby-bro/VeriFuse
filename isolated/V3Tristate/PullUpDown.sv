module PullUpDown (
    output wire out_pull,
    inout wire tri_pulled,
    input wire data_in
);
    pullup (tri_pulled);
    assign out_pull = tri_pulled;
endmodule


module ContinuousWire (
    input logic din,
    output wire dout
);
    wire internal_w;
    assign internal_w = din;
    assign dout       = internal_w;
endmodule


module multiplexer_2to1 (
    input logic sel,
    output logic result,
    input logic data0,
    input logic data1
);
    assign result = sel ? data1 : data0;
endmodule


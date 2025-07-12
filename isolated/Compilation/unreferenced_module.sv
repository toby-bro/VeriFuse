module unreferenced_module (
    input logic unused_in,
    output logic unused_out
);
    assign unused_out = ~unused_in;
endmodule


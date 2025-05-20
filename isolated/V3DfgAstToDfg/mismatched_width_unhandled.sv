module mismatched_width_unhandled (
    output logic [3:0] out,
    input logic [7:0] in
);
    assign out = in;
endmodule


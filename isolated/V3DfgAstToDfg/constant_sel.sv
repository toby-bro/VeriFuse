module constant_sel (
    output logic out2,
    input logic [31:0] in,
    output logic [7:0] out1
);
    assign out1 = in[15:8];
    assign out2 = in[3];
endmodule


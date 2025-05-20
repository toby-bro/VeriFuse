module ModVectorAdd (
    input logic [7:0] in_v,
    output logic [7:0] out_v
);
    assign out_v = in_v + 8'h01;
endmodule


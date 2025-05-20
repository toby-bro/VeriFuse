module concat_op (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out_c
);
    assign out_c = {in_h, in_l};
endmodule


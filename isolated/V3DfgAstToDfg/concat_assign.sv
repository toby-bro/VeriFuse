module concat_assign (
    output logic [3:0] out_h,
    output logic [3:0] out_l,
    input logic [7:0] in
);
    assign {out_h, out_l} = in;
endmodule


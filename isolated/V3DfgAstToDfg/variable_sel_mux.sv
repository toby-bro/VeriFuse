module variable_sel_mux (
    output logic out,
    input logic [7:0] in,
    input logic [2:0] index
);
    assign out = in[index];
endmodule


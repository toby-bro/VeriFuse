module bug (
    output logic [3:0] o
);
    localparam logic [3:0] L1 = '1;
    assign o = L1;
endmodule

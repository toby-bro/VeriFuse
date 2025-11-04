module test (
    input logic i,
    output logic [3:0] o
);
    localparam logic [3:0] L0  = '0;
    localparam logic [3:0] L1  = '1;
    localparam logic [3:0] COMB = L0 | L1;
   
    assign o = COMB ^ {3'b000, i};
endmodule

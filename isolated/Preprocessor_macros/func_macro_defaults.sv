module func_macro_defaults (
    input logic en,
    output logic [7:0] default_out
);
    `define DEFAULT_CONST       8'hAA
    `define CALC(val, def=`DEFAULT_CONST) ((val) | (def))
    localparam logic [7:0] P_WITH_DEF     = `CALC(8'h0F);
    localparam logic [7:0] P_OVERRIDE_DEF = `CALC(8'hF0, 8'h11);
    assign default_out = en ? P_WITH_DEF : P_OVERRIDE_DEF;
endmodule


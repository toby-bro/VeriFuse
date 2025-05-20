module div_mod_ops (
    output logic [15:0] quotient,
    output logic [7:0] remainder,
    input logic [15:0] numerator,
    input logic [7:0] denominator,
    input logic [15:0] dividend_mod,
    input logic [7:0] divisor_mod
);
    assign quotient = numerator / denominator;
    assign remainder = dividend_mod % divisor_mod;
endmodule


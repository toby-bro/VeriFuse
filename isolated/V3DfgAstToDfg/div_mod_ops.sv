module div_mod_ops (
    input logic [7:0] denominator,
    input logic [15:0] dividend_mod,
    input logic [7:0] divisor_mod,
    input logic [15:0] numerator,
    output logic [15:0] quotient,
    output logic [7:0] remainder
);
    assign quotient = (denominator == 0) ? 16'hFFFF : (numerator / denominator); 
    assign remainder = (divisor_mod == 0) ? 8'hFF : (dividend_mod % divisor_mod);
endmodule


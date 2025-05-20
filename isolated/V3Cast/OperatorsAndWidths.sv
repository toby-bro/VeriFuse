module OperatorsAndWidths (
    input logic [63:0] in_64,
    output logic [31:0] out_compare,
    output logic [63:0] out_shift,
    input logic [15:0] in_16,
    output logic [31:0] out_logic,
    input logic [31:0] in_32,
    output logic [31:0] out_arith,
    output logic [31:0] out_unary,
    input logic [7:0] in_8
);
    logic [31:0] temp_arith;
    logic [31:0] temp_logic;
    logic [63:0] temp_shift;
    assign temp_arith = in_8 + in_16; 
    assign temp_logic = in_16 & in_32; 
    assign out_arith = temp_arith;
    assign out_logic = temp_logic;
    assign out_compare = (in_8 == in_16) ? 1 : 0; 
    assign out_unary = -in_8; 
    assign temp_logic = temp_logic | !in_16; 
    assign out_logic = temp_logic; 
    assign temp_arith = in_32 % 10; 
    assign out_arith = temp_arith; 
    assign temp_shift = in_64 << in_8; 
    assign out_shift = temp_shift;
endmodule


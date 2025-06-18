module Mod_BasicOps (
    input wire [7:0] in_a,
    input wire [7:0] in_b,
    input wire in_bit,
    input wire [7:0] in_c,
    input wire [7:0] in_const1,
    input wire [7:0] in_const2,
    output logic [7:0] out_add_assoc,
    output logic [7:0] out_and_assoc,
    output logic [7:0] out_and_swap_const,
    output logic [7:0] out_arith,
    output logic [7:0] out_bitwise,
    output logic out_logical,
    output logic [7:0] out_mul_assoc,
    output logic [7:0] out_negate,
    output logic [7:0] out_or_assoc,
    output logic [7:0] out_or_swap_not,
    output logic [7:0] out_unary_not,
    output logic [7:0] out_xor_assoc,
    output logic [7:0] out_xor_swap_var
);
    logic [7:0] intermediate_arith;
    logic [7:0] intermediate_bitwise;
    logic [0:0] intermediate_logical;
    logic [7:0] intermediate_add_assoc;
    logic [7:0] intermediate_mul_assoc;
    logic [7:0] intermediate_and_assoc;
    logic [7:0] intermediate_or_assoc;
    logic [7:0] intermediate_xor_assoc;
    parameter [7:0] CONST_ZERO = 8'h00;
    always_comb begin
        intermediate_arith = in_a;
        intermediate_arith = intermediate_arith + in_b;
        intermediate_arith = intermediate_arith - in_c;
        intermediate_arith = intermediate_arith * in_const1;
        if (in_b != CONST_ZERO) begin
            intermediate_arith = intermediate_arith / in_b;
            intermediate_arith = intermediate_arith % in_b;
        end else begin
            intermediate_arith = 'x;
        end
        out_arith = intermediate_arith;
        intermediate_bitwise = in_a;
        intermediate_bitwise = intermediate_bitwise & in_b;
        intermediate_bitwise = intermediate_bitwise | in_c;
        intermediate_bitwise = intermediate_bitwise ^ in_const1;
        out_bitwise = intermediate_bitwise;
        intermediate_logical = (in_a != CONST_ZERO) && (in_b != CONST_ZERO);
        intermediate_logical = intermediate_logical || (in_c != CONST_ZERO);
        out_logical = !intermediate_logical;
        out_unary_not = ~in_a;
        out_negate = -in_a;
        intermediate_add_assoc = (in_a + in_b) + in_c;
        out_add_assoc = intermediate_add_assoc;
        intermediate_mul_assoc = (in_a * in_b) * in_c;
        out_mul_assoc = intermediate_mul_assoc;
        intermediate_and_assoc = (in_a & in_b) & in_c;
        out_and_assoc = intermediate_and_assoc;
        intermediate_or_assoc = (in_a | in_b) | in_c;
        out_or_assoc = intermediate_or_assoc;
        intermediate_xor_assoc = (in_a ^ in_b) ^ in_c;
        out_xor_assoc = intermediate_xor_assoc;
        out_and_swap_const = in_const1 & in_a;
        out_or_swap_not = (~in_a) | in_b;
        out_xor_swap_var = in_b ^ in_c;
    end
endmodule


module assign_basic #(
    parameter int SIZE = 8
) (
    input logic clk,
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input int in_int,
    input real in_real,
    input logic rst_n,
    output logic [7:0] out_and_eq,
    output logic [7:0] out_ashr_eq,
    output logic [7:0] out_assign,
    output logic [7:0] out_conv_int,
    output int out_conv_real,
    output logic [7:0] out_conv_real_explicit,
    output logic [7:0] out_div_eq,
    output logic [7:0] out_minus_eq,
    output logic [7:0] out_mod_eq,
    output logic [7:0] out_mult_eq,
    output logic [7:0] out_non_blocking,
    output logic [7:0] out_or_eq,
    output logic [7:0] out_plus_eq,
    output logic [7:0] out_shl_eq,
    output logic [7:0] out_shr_eq,
    output logic [7:0] out_xor_eq
);
    logic [SIZE-1:0] reg_assign;
    logic [SIZE-1:0] reg_plus_eq;
    logic [SIZE-1:0] reg_minus_eq;
    logic [SIZE-1:0] reg_mult_eq;
    logic [SIZE-1:0] reg_div_eq;
    logic [SIZE-1:0] reg_mod_eq;
    logic [SIZE-1:0] reg_and_eq;
    logic [SIZE-1:0] reg_or_eq;
    logic [SIZE-1:0] reg_xor_eq;
    logic [SIZE-1:0] reg_shl_eq;
    logic [SIZE-1:0] reg_shr_eq;
    logic [SIZE-1:0] reg_ashr_eq;
    logic [SIZE-1:0] reg_non_blocking;
    logic [SIZE-1:0] reg_conv_int;
    int              reg_conv_real;
    logic [SIZE-1:0] reg_conv_real_explicit;
    always_comb begin
        reg_assign = in_a;
        reg_plus_eq = in_a;
        reg_plus_eq += in_b;
        reg_minus_eq = in_a;
        reg_minus_eq -= in_b;
        reg_mult_eq = in_a;
        reg_mult_eq *= in_b;
        if (in_b != 0) begin
            reg_div_eq = in_a;
            reg_div_eq /= in_b;
            reg_mod_eq = in_a;
            reg_mod_eq %= in_b;
        end else begin
            reg_div_eq = 'x;
            reg_mod_eq = 'x;
        end
        reg_and_eq = in_a;
        reg_and_eq &= in_b;
        reg_or_eq = in_a;
        reg_or_eq |= in_b;
        reg_xor_eq = in_a;
        reg_xor_eq ^= in_b;
        reg_shl_eq = in_a;
        if (SIZE > 0) reg_shl_eq <<= in_int % SIZE; else reg_shl_eq = '0;
        reg_shr_eq = in_a;
        if (SIZE > 0) reg_shr_eq >>= in_int % SIZE; else reg_shr_eq = '0;
        reg_ashr_eq = $signed(in_a);
        if (SIZE > 0) reg_ashr_eq >>>= in_int % SIZE; else reg_ashr_eq = '0;
        reg_conv_int = in_int;
        reg_conv_real = int'(in_real);
        reg_conv_real_explicit = logic'(in_real);
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_non_blocking <= '0;
        end else begin
            reg_non_blocking <= in_a + in_b;
        end
    end
    assign out_assign = reg_assign;
    assign out_plus_eq = reg_plus_eq;
    assign out_minus_eq = reg_minus_eq;
    assign out_mult_eq = reg_mult_eq;
    assign out_div_eq = reg_div_eq;
    assign out_mod_eq = reg_mod_eq;
    assign out_and_eq = reg_and_eq;
    assign out_or_eq = reg_or_eq;
    assign out_xor_eq = reg_xor_eq;
    assign out_shl_eq = reg_shl_eq;
    assign out_shr_eq = reg_shr_eq;
    assign out_ashr_eq = reg_ashr_eq;
    assign out_non_blocking = reg_non_blocking;
    assign out_conv_int = reg_conv_int;
    assign out_conv_real = reg_conv_real;
    assign out_conv_real_explicit = reg_conv_real_explicit;
endmodule


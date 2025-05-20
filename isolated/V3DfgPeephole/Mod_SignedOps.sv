module Mod_SignedOps (
    output logic signed [7:0] out_sdiv,
    output logic signed [7:0] out_smul,
    output logic signed [7:0] out_pow_ss,
    output logic out_sgte,
    input wire [7:0] in_u,
    input wire [3:0] in_shift_u,
    output logic signed [7:0] out_shift_rs_signed,
    output logic out_slte,
    output logic [7:0] out_pow_us,
    input wire signed [3:0] in_shift_sa,
    input wire signed [3:0] in_narrow_sa,
    input wire signed [7:0] in_sb,
    output logic signed [7:0] out_smod,
    output logic signed [7:0] out_sext,
    output logic signed [7:0] out_pow_su,
    output logic out_sgt,
    output logic out_slt,
    input wire signed [7:0] in_sa
);
    logic signed [7:0] intermediate_sdiv;
    logic signed [7:0] intermediate_smod;
    always_comb begin
        if (in_sb != 8'd0) begin
            intermediate_sdiv = in_sa / in_sb;
            intermediate_smod = in_sa % in_sb;
        end else begin
            intermediate_sdiv = 'x;
            intermediate_smod = 'x;
        end
        out_sdiv = intermediate_sdiv;
        out_smod = intermediate_smod;
        out_smul = in_sa * in_sb;
        out_sgt = (in_sa > in_sb);
        out_slt = (in_sa < in_sb);
        out_sgte = (in_sa >= in_sb);
        out_slte = (in_sa <= in_sb);
        out_shift_rs_signed = in_sa >>> in_shift_u;
        out_sext = $signed(in_narrow_sa);
        out_pow_ss = in_sa ** in_shift_sa;
        out_pow_su = in_sa ** in_shift_u;
        out_pow_us = in_u ** in_shift_sa;
    end
endmodule


module SignedUnsignedConversions (
    input integer in_int,
    input logic [31:0] in_l32,
    input logic signed [7:0] in_s8,
    input logic [15:0] in_u16,
    output logic signed [15:0] out_s16,
    output logic signed [31:0] out_s32_from_int,
    output logic signed [31:0] out_s32_from_l32,
    output logic [31:0] out_u32_from_int,
    output logic [31:0] out_u32_from_l32,
    output logic [7:0] out_u8
);
    always_comb begin
        out_u8 = $unsigned(in_s8);
        out_s16 = $signed(in_u16);
        out_s32_from_l32 = $signed(in_l32);
        out_u32_from_l32 = $unsigned(in_l32);
        out_s32_from_int = $signed(in_int);
        out_u32_from_int = $unsigned(in_int);
    end
endmodule


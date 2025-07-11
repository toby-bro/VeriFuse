module SignedUnsignedConversions (
  input logic signed [7:0] in_s8,
  input logic unsigned [15:0] in_u16,
  input logic [31:0] in_l32,
  input integer in_int,
  output logic [7:0] out_u8,
  output logic signed [15:0] out_s16,
  output logic signed [31:0] out_s32_from_l32,
  output logic unsigned [31:0] out_u32_from_l32,
  output logic signed [31:0] out_s32_from_int,
  output logic unsigned [31:0] out_u32_from_int
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
module RtoiConversion (
  input real in_r,
  output integer out_i
);
  always_comb begin
    out_i = $rtoi(in_r);
  end
endmodule
module ItorConversion (
  input integer in_i,
  input logic [63:0] in_l64,
  input logic signed [19:0] in_s20,
  output real out_r_from_i,
  output real out_r_from_l64,
  output real out_r_from_s20
);
  always_comb begin
    out_r_from_i = $itor(in_i);
    out_r_from_l64 = $itor(in_l64);
    out_r_from_s20 = $itor(in_s20);
  end
endmodule
module RealBitsConversion (
  input real in_r,
  input longint unsigned in_lib,
  output longint unsigned out_rib,
  output real out_bir
);
  always_comb begin
    out_rib = $realtobits(in_r);
    out_bir = $bitstoreal(in_lib);
  end
endmodule
module ShortRealBitsConversion (
  input shortreal in_sr,
  input int unsigned in_iub,
  output int unsigned out_srib,
  output shortreal out_bisr
);
  always_comb begin
    out_srib = $shortrealtobits(in_sr);
    out_bisr = $bitstoshortreal(in_iub);
  end
endmodule

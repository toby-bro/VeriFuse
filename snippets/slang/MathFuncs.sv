module Clog2Coverage (
    input int unsigned data_in,
    output int clog2_out
);
always @(*) begin
    clog2_out = $clog2(data_in);
end
endmodule
module CountBitsCoverage (
    input logic [7:0] vector_in,
    output int countbits_0_out,
    output int countbits_1_out,
    output int countbits_x_out,
    output int countbits_z_out,
    output int countbits_01_out,
    output int countbits_01xz_out
);
always @(*) begin
    countbits_0_out = $countbits(vector_in, 1'b0);
    countbits_1_out = $countbits(vector_in, 1'b1);
    countbits_x_out = $countbits(vector_in, 1'bx);
    countbits_z_out = $countbits(vector_in, 1'bz);
    countbits_01_out = $countbits(vector_in, 1'b0, 1'b1);
    countbits_01xz_out = $countbits(vector_in, 1'b0, 1'b1, 1'bx, 1'bz);
end
endmodule
module CountOnesCoverage (
    input logic [15:0] vector_in,
    output int countones_out
);
always @(*) begin
    countones_out = $countones(vector_in);
end
endmodule
module BooleanBVCFuncsCoverage (
    input logic [3:0] vector_in,
    output bit onehot_out,
    output bit onehot0_out,
    output bit isunknown_out
);
always @(*) begin
    onehot_out = $onehot(vector_in);
    onehot0_out = $onehot0(vector_in);
    isunknown_out = $isunknown(vector_in);
end
endmodule
module RealMath1FuncsCoverage (
    input real real_in,
    output real ln_out,
    output real log10_out,
    output real exp_out,
    output real sqrt_out,
    output real floor_out,
    output real ceil_out,
    output real sin_out,
    output real cos_out,
    output real tan_out,
    output real asin_out,
    output real acos_out,
    output real atan_out,
    output real sinh_out,
    output real cosh_out,
    output real tanh_out,
    output real asinh_out,
    output real acosh_out,
    output real atanh_out
);
always @(*) begin
    ln_out = $ln(real_in);
    log10_out = $log10(real_in);
    exp_out = $exp(real_in);
    sqrt_out = $sqrt(real_in);
    floor_out = $floor(real_in);
    ceil_out = $ceil(real_in);
    sin_out = $sin(real_in);
    cos_out = $cos(real_in);
    tan_out = $tan(real_in);
    asin_out = $asin(real_in);
    acos_out = $acos(real_in);
    atan_out = $atan(real_in);
    sinh_out = $sinh(real_in);
    cosh_out = $cosh(real_in);
    tanh_out = $tanh(real_in);
    asinh_out = $asinh(real_in);
    acosh_out = $acosh(real_in);
    atanh_out = $atanh(real_in);
end
endmodule
module RealMath2FuncsCoverage (
    input real real_in_a,
    input real real_in_b,
    output real pow_out,
    output real atan2_out,
    output real hypot_out
);
always @(*) begin
    pow_out = $pow(real_in_a, real_in_b);
    atan2_out = $atan2(real_in_a, real_in_b);
    hypot_out = $hypot(real_in_a, real_in_b);
end
endmodule

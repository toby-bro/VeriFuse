module RealMath1FuncsCoverage (
    input real real_in,
    output real acos_out,
    output real acosh_out,
    output real asin_out,
    output real asinh_out,
    output real atan_out,
    output real atanh_out,
    output real ceil_out,
    output real cos_out,
    output real cosh_out,
    output real exp_out,
    output real floor_out,
    output real ln_out,
    output real log10_out,
    output real sin_out,
    output real sinh_out,
    output real sqrt_out,
    output real tan_out,
    output real tanh_out
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


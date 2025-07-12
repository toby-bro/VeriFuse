module RealMath2FuncsCoverage (
    input real real_in_a,
    input real real_in_b,
    output real atan2_out,
    output real hypot_out,
    output real pow_out
);
always @(*) begin
    pow_out = $pow(real_in_a, real_in_b);
    atan2_out = $atan2(real_in_a, real_in_b);
    hypot_out = $hypot(real_in_a, real_in_b);
end
endmodule


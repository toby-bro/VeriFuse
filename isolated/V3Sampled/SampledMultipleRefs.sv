module SampledMultipleRefs (
    input logic [3:0] in_control,
    output logic out_eq_zero,
    output logic out_msb
);
    assign out_eq_zero = ($sampled(in_control) == 4'b0000);
    assign out_msb = $sampled(in_control)[3];
endmodule


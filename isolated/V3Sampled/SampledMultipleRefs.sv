module SampledMultipleRefs (
    output logic out_eq_zero,
    output logic out_msb,
    input logic [3:0] in_control
);
    assign out_eq_zero = ($sampled(in_control) == 4'b0000);
    assign out_msb = $sampled(in_control)[3];
endmodule


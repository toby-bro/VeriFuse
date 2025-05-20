module SampledCombinedExpr (
    input logic a_in,
    input logic b_in,
    output logic out_and
);
    assign out_and = $sampled(a_in) && $sampled(b_in);
endmodule


module SampledCombinedExpr (
    output logic out_and,
    input logic a_in,
    input logic b_in
);
    assign out_and = $sampled(a_in) && $sampled(b_in);
endmodule


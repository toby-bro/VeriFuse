module SampledBasic (
    input logic in_val,
    output logic out_val
);
    assign out_val = $sampled(in_val);
endmodule


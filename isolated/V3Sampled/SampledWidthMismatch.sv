module SampledWidthMismatch (
    input logic [15:0] wide_in,
    output logic [7:0] narrow_out
);
    assign narrow_out = $sampled(wide_in[7:0]);
endmodule


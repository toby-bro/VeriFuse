module SampledWidthMismatch (
    output logic [7:0] narrow_out,
    input logic [15:0] wide_in
);
    assign narrow_out = $sampled(wide_in[7:0]);
endmodule


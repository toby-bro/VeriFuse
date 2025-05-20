module SampledPartOfVector (
    input logic [7:0] vec_in,
    output logic out_bit
);
    assign out_bit = $sampled(vec_in[4]);
endmodule


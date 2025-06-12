module SampledStructLike (
    input logic [2:0] field_a,
    input logic [1:0] field_b,
    output logic out_result
);
    logic [4:0] combined_fields;
    assign combined_fields = {field_a, field_b};
    assign out_result = $sampled(combined_fields[3]);
endmodule


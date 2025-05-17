module SampledBasic (
    input logic in_val,
    output logic out_val
);
  assign out_val = $sampled(in_val);
endmodule
module SampledInternalWire (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
  logic [7:0] internal_wire;
  assign internal_wire = in_data << 1;
  assign out_data = $sampled(internal_wire);
endmodule
module SampledMultipleRefs (
    input logic [3:0] in_control,
    output logic out_eq_zero,
    output logic out_msb
);
  assign out_eq_zero = ($sampled(in_control) == 4'b0000);
  assign out_msb = $sampled(in_control)[3];
endmodule
module SampledCombinedExpr (
    input logic a_in,
    input logic b_in,
    output logic out_and
);
  assign out_and = $sampled(a_in) && $sampled(b_in);
endmodule
module SampledWidthMismatch (
    input logic [15:0] wide_in,
    output logic [7:0] narrow_out
);
  assign narrow_out = $sampled(wide_in[7:0]);
endmodule
module SampledPartOfVector (
    input logic [7:0] vec_in,
    output logic out_bit
);
  assign out_bit = $sampled(vec_in[4]);
endmodule
module SampledStructLike (
    input logic [2:0] field_a,
    input logic [1:0] field_b,
    output logic out_result
);
  logic [4:0] combined_fields;
  assign combined_fields = {field_a, field_b};
  assign out_result = $sampled(combined_fields[3]);
endmodule

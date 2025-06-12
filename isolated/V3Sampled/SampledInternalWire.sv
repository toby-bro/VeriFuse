module SampledInternalWire (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] internal_wire;
    assign internal_wire = in_data << 1;
    assign out_data = $sampled(internal_wire);
endmodule


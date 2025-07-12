module TimeScaleDeclarationModule (
    input logic dummy_in_ts,
    output logic dummy_out_ts
);
    timeunit      10ns;
    timeprecision 100ps;
    assign dummy_out_ts = dummy_in_ts;
endmodule


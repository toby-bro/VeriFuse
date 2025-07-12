module child_concat_output (
    input logic dummy_in,
    output logic [7:0] data
);
    assign data = dummy_in ? 8'hAA : 8'h55;
endmodule


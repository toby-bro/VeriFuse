module ansi_directions (
    input logic control_in,
    input logic data_ref_in,
    output logic data_ref_out,
    output logic status_out,
    inout wire data_inout
);
    logic internal_data = 1'b0;
    assign data_inout = internal_data;
    always_comb begin
        data_ref_out = data_ref_in;
        internal_data = data_inout;
        status_out = internal_data | control_in;
    end
endmodule


module modport_access_diag_mod (
    input logic dummy_in,
    input logic mp_valid,
    output logic dummy_out,
    output logic out_val
);
    logic temp_valid_madm = mp_valid;
    always_comb begin
        out_val   = temp_valid_madm;
        dummy_out = dummy_in;
    end
endmodule


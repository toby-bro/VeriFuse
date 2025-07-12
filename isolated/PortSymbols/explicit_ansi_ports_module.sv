module explicit_ansi_ports_module (
    input logic dummy_in_ansi,
    output logic dummy_out_ansi
);
    logic in_explicit;
    logic out_explicit;
    always_comb begin
        out_explicit = in_explicit;
        dummy_out_ansi = dummy_in_ansi;
    end
endmodule


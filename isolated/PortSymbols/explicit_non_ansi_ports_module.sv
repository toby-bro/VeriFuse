module explicit_non_ansi_ports_module (
    dummy_in_non_ansi,
    named_conn_in,
    dummy_out_non_ansi,
    named_conn_out
);
    input logic named_conn_in;
    output logic named_conn_out;
    input logic dummy_in_non_ansi;
    output logic dummy_out_non_ansi;
    assign named_conn_out = named_conn_in;
    assign dummy_out_non_ansi = dummy_in_non_ansi;
endmodule


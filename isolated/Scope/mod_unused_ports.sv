module mod_unused_ports (
    input wire unused_in,
    output logic unused_out
);
    assign unused_out = unused_in;
endmodule


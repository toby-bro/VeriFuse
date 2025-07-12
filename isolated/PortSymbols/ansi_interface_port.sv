module ansi_interface_port (
    input logic interface_input,
    output logic interface_output
);
    always_comb begin
        iface_port.signal_b = iface_port.signal_a;
        interface_output = interface_input;
    end
endmodule


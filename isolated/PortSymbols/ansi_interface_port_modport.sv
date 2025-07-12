interface my_if;
    logic signal_a;
    logic signal_b;
    modport mp (
        input signal_a,
        output signal_b
    );
endinterface
module ansi_interface_port_modport (
    my_if.mp iface_port_mp,
    input logic modport_input,
    output logic modport_output
);
    always_comb begin
        iface_port_mp.signal_b = iface_port_mp.signal_a;
        modport_output = modport_input;
    end
endmodule


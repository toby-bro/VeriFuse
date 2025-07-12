module child_iface_port (
    input logic iface_child_input,
    output logic iface_child_output
);
    assign if_inst.signal_b = ~if_inst.signal_a;
    assign iface_child_output = iface_child_input;
endmodule


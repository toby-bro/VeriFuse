module iface_array_port_child (
    input logic array_in,
    output logic array_out
);
    always_comb begin
        iface_array_port[0].data = array_in ? 8'hAA : 8'h55;
        iface_array_port[1].data = array_in ? 8'h55 : 8'hAA;
        array_out = array_in;
    end
endmodule


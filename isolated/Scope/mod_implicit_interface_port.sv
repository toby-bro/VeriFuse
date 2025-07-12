interface intf_implicit_port;
    wire data;
endinterface
module mod_implicit_interface_port (
    input bit clk,
    output logic [3:0] out_data
);
    intf_implicit_port implicit_intf ();
    assign out_data = implicit_intf.data;
endmodule


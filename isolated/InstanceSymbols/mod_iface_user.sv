interface my_interface #(
    parameter int WIDTH = 8
) (
    input logic clk,
    output logic [7:0] data
);
    logic [WIDTH-1:0] internal_data;
    modport mp (
        input clk,
        output data
    );
    assign data = internal_data;
endinterface
module mod_iface_user (
    input logic i_clk,
    output logic [7:0] i_data
);
    my_interface #(.WIDTH(8)) iface_inst (.clk(i_clk), .data(i_data));
endmodule


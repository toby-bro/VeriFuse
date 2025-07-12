module mod_delay_net #(
    parameter int D = 5
) (
    input wire data_in,
    output wire data_out
);
    wire #(D) net_dly = data_in;
    assign data_out = net_dly;
endmodule


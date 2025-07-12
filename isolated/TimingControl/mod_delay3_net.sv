module mod_delay3_net #(
    parameter int D1 = 1,
    parameter int D2 = 2,
    parameter int D3 = 3
) (
    input wire data_in,
    output wire data_out
);
    wire #(D1:D2:D3) net_dly = data_in;
    assign data_out = net_dly;
endmodule


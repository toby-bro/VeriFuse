module mod_delay_net_real_param (
    input wire data_in,
    output wire data_out
);
    parameter real R_PARAM = 3.14;
    wire #(R_PARAM) net_dly_param = data_in;
    assign data_out = net_dly_param;
endmodule


module mod_delay3_syntax (
    input wire data_in,
    output wire data_out
);
    wire #(1:2:3) net_dly = data_in;
    assign data_out = net_dly;
endmodule


module BufIfGate (
    input wire data_in,
    input wire enable_in,
    output wire out_bufif
);
    bufif1 b1 (out_bufif, data_in, enable_in);
endmodule


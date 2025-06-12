module BufIfGate (
    output wire out_bufif,
    input wire data_in,
    input wire enable_in
);
    bufif1 b1 (out_bufif, data_in, enable_in);
endmodule


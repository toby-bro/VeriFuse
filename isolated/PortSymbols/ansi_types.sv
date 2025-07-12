module ansi_types (
    input logic [7:0] byte_in,
    input int data_int,
    output bit [7:0] byte_out,
    output real data_real
);
    always_comb begin
        byte_out = byte_in + 1;
        data_real = data_int;
    end
endmodule


module MultiplePortsAndTypes (
    input byte b_in,
    output int i_out,
    input bit flag,
    input logic [3:0] small_val
);
    logic [7:0] temp_byte;
    always_comb begin
        if (flag) begin
            temp_byte = {4'h0, small_val};
        end else begin
            temp_byte = b_in;
        end
    end
    assign i_out = temp_byte;
endmodule


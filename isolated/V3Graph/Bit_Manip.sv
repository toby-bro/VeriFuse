module Bit_Manip (
    input wire [1:0] byte_idx,
    input wire [31:0] wide_data,
    output reg [7:0] selected_byte
);
    always_comb begin
        case (byte_idx)
            2'b00: selected_byte = wide_data[7:0];
            2'b01: selected_byte = wide_data[15:8];
            2'b10: selected_byte = wide_data[23:16];
            default: selected_byte = wide_data[31:24];
        endcase
    end
endmodule


module Comb_Case (
    input wire [3:0] in2,
    input wire [3:0] in3,
    output reg [3:0] mux_out,
    input wire [1:0] sel,
    input wire [3:0] in0,
    input wire [3:0] in1
);
    always_comb begin
        case (sel)
            2'b00: mux_out = in0;
            2'b01: mux_out = in1;
            2'b10: mux_out = in2;
            default: mux_out = in3;
        endcase
    end
endmodule


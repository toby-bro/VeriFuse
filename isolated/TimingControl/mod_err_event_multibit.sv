module mod_err_event_multibit (
    input wire clk,
    input wire [2:0] multi_bit_in,
    output logic dummy
);
    always @(posedge multi_bit_in) begin
        dummy = ~dummy;
    end
endmodule


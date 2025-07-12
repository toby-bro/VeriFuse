module mod_event_any_multibit (
    input wire [1:0] array_in,
    input wire clk,
    output logic dummy
);
    always @(array_in) begin
        dummy = ~dummy;
    end
endmodule


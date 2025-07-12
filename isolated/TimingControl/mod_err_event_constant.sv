module mod_err_event_constant (
    input wire clk,
    output logic dummy
);
    always @(posedge 1'b1) begin
        dummy = ~dummy;
    end
endmodule


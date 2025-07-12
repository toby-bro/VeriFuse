module mod_err_event_iff_nonbool (
    input wire clk,
    input wire [1:0] condition_in,
    output logic dummy
);
    always @(posedge clk iff condition_in) begin
        dummy = ~dummy;
    end
endmodule


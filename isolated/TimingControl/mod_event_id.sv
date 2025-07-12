module mod_event_id (
    input wire clk,
    output reg fired
);
    event my_event;
    always @(posedge clk) begin
        -> my_event;
    end
    always @(my_event) begin
        fired = ~fired;
    end
endmodule


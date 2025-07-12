module event_trigger_mod (
    input logic clk,
    input logic trigger_in,
    output logic event_occured
);
    event my_event;
    static logic event_triggered = 0;
    always @(posedge clk) begin
        if (trigger_in) begin
            -> my_event; 
        end else begin
            ->> @(posedge clk) my_event; 
        end
    end
    always @(my_event) begin
        event_triggered = ~event_triggered;
    end
    assign event_occured = event_triggered;
endmodule


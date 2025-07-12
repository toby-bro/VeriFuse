module EventTriggeredFunc (
    input logic clk,
    input bit dummy_input,
    input bit trigger_in,
    output bit dummy_output,
    output logic triggered_out
);
    event my_event;
    always_ff @(posedge clk) begin
        if (trigger_in) -> my_event;
    end
    always @(my_event) begin
        triggered_out = my_event.triggered;
    end
    always_comb begin
        dummy_output = dummy_input;
    end
endmodule


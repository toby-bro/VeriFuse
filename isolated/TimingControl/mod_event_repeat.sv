module mod_event_repeat (
    input wire clk,
    input wire [7:0] count,
    output reg toggle
);
    always @(posedge clk) begin
        repeat (count) @(posedge clk);
        toggle <= ~toggle;
    end
endmodule


module mod_event_posedge (
    input wire clk,
    input wire data_in,
    output reg data_out
);
    always @(posedge clk) begin
        data_out <= data_in;
    end
endmodule


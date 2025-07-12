module mod_event_list (
    input wire clk,
    input wire data_in,
    input wire enable,
    input wire rst,
    output reg out_event_list
);
    always @(posedge clk or negedge rst or enable or data_in) begin
        out_event_list <= 1'b1;
    end
endmodule


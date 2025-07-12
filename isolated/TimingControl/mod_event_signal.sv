module mod_event_signal (
    input wire clk,
    input wire data_in,
    input wire [1:0] edge_in,
    input wire rst,
    output reg out_clk_pos,
    output reg out_data_any,
    output reg out_edge_specific,
    output reg out_rst_neg
);
    always @(posedge clk) begin
        out_clk_pos <= 1'b1;
    end
    always @(negedge rst) begin
        out_rst_neg <= 1'b1;
    end
    always @(data_in) begin
        out_data_any <= data_in;
    end
        always @(posedge edge_in) begin
            out_edge_specific <= 1'b1;
        end
endmodule


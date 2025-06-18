module simple_seq (
    input wire clk,
    input wire [2:0] count_in,
    input wire reset,
    output wire [2:0] count_out
);
    reg [2:0] counter_reg;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter_reg <= 3'b000;
        end else begin
            counter_reg <= count_in + 3'b001;
        end
    end
    assign count_out = counter_reg;
endmodule


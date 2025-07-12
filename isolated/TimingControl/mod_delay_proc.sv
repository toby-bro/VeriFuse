module mod_delay_proc (
    input wire clk,
    input wire [7:0] delay_val,
    output reg [7:0] out_delay
);
    always @(posedge clk) begin
        #(delay_val) out_delay <= delay_val;
    end
endmodule


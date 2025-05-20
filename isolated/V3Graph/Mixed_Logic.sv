module Mixed_Logic (
    input wire [7:0] data_in,
    input wire control,
    output reg [7:0] data_reg,
    output wire [7:0] data_comb,
    input wire clk
);
    assign data_comb = data_in ^ {8{control}};
      always_ff @(posedge clk) begin
    data_reg <= data_comb;
      end
endmodule


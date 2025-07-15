module Mixed_Logic (
    input wire clk,
    input wire control,
    input wire [7:0] data_in,
    output wire [7:0] data_comb,
    output reg [7:0] data_reg
);
    assign data_comb = data_in ^ {8{control}};
    always_ff @(posedge clk) begin
        data_reg <= data_comb;
    end
endmodule


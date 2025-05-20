module Comb_IfElse (
    input wire [15:0] value2,
    output reg [15:0] result_val,
    input wire condition,
    input wire [15:0] value1
);
    always_comb begin
    if (condition) begin
      result_val = value1;
    end else begin
      result_val = value2;
    end
      end
endmodule


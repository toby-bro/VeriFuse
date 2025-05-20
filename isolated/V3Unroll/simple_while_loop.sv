module simple_while_loop (
    input logic [3:0] in_val,
    output logic [7:0] out_prod
);
    logic [7:0] prod;
      logic [3:0] j;
      always_comb begin
    prod = 8'h01;
    j = in_val;
    while (j > 0) begin
      prod = prod * 2;
      j = j - 1;
    end
    out_prod = prod;
      end
endmodule


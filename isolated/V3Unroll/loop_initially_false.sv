module loop_initially_false (
    input logic [3:0] initial_counter,
    output logic [7:0] result_check
);
    logic [7:0] res;
      always_comb begin
    res = 8'h11; 
    for (int l = initial_counter; l < initial_counter - 1; l = l + 1) begin
      res = res + 2; 
    end
    result_check = res;
      end
endmodule


module simple_for_loop (
  input logic [7:0] in_data,
  output logic [7:0] out_sum
);
  logic [7:0] sum;
  always_comb begin
    sum = 8'h00;
    for (int i = 0; i < 5; i = i + 1) begin
      sum = sum + in_data;
    end
    out_sum = sum;
  end
endmodule
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
module generate_for_block (
  input logic [1:0] selector,
  output logic [7:0] selected_output
);
  wire [7:0] data [3:0]; 
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : data_gen
      assign data[i] = 8'(i + 1) * 8'(i + 1);
    end
  endgenerate
  always_comb begin
    case (selector)
      0: selected_output = data[0];
      1: selected_output = data[1];
      2: selected_output = data[2];
      3: selected_output = data[3];
      default: selected_output = 8'hXX;
    endcase
  end
endmodule
module loop_with_internal_assign (
  input logic [3:0] start_val,
  output logic [7:0] final_val
);
  logic [7:0] current_val;
  always_comb begin
    current_val = start_val;
    for (int k = 0; k < 3; k = k + 1) begin
      current_val = current_val + 1;
    end
    final_val = current_val;
  end
endmodule
module loop_with_begin_end (
  input logic [2:0] count_limit,
  input logic [7:0] data_in,
  output logic [7:0] accumulated_xor
);
  logic [7:0] accum_xor_reg;
  always_comb begin
    accum_xor_reg = 8'hFF; 
    for (int iter = 0; iter < count_limit; iter = iter + 1) begin : loop_block
      accum_xor_reg = accum_xor_reg ^ data_in;
      accum_xor_reg = accum_xor_reg + 1;
    end
    accumulated_xor = accum_xor_reg;
  end
endmodule
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
module loop_unroll_limit_test (
    input logic [1:0] large_data_in,
    output logic [7:0] large_sum_out
);
    logic [7:0] current_large_sum;
    always_comb begin
        current_large_sum = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum = current_large_sum + large_data_in[0];
            current_large_sum = current_large_sum + large_data_in[1];
            current_large_sum = current_large_sum + 1;
        end
        large_sum_out = current_large_sum;
    end
endmodule

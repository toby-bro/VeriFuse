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


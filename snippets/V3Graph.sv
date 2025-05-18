module Comb_Assign (
  input wire in1,
  input wire in2,
  output wire out
);
  assign out = in1 & in2;
endmodule
module Seq_DFF (
  input wire clk,
  input wire rst,
  input wire [7:0] d_in,
  output reg [7:0] q_out
);
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      q_out <= 8'b0;
    end else begin
      q_out <= d_in;
    end
  end
endmodule
module Comb_Case (
  input wire [1:0] sel,
  input wire [3:0] in0,
  input wire [3:0] in1,
  input wire [3:0] in2,
  input wire [3:0] in3,
  output reg [3:0] mux_out
);
  always_comb begin
    case (sel)
      2'b00: mux_out = in0;
      2'b01: mux_out = in1;
      2'b10: mux_out = in2;
      default: mux_out = in3;
    endcase
  end
endmodule
module Comb_Loop (
  input wire loop_in,
  output wire loop_out
);
  wire loop_wire1;
  wire loop_wire2;
  assign loop_wire1 = loop_wire2 | loop_in;
  assign loop_wire2 = loop_wire1; 
  assign loop_out = loop_wire1;
endmodule
module Mixed_Logic (
  input wire clk,
  input wire [7:0] data_in,
  input wire control,
  output reg [7:0] data_reg,
  output wire [7:0] data_comb
);
  assign data_comb = data_in ^ {8{control}};
  always_ff @(posedge clk) begin
    data_reg <= data_comb;
  end
endmodule
module Bit_Manip (
  input wire [31:0] wide_data,
  input wire [1:0] byte_idx,
  output reg [7:0] selected_byte
);
  always_comb begin
    case (byte_idx)
      2'b00: selected_byte = wide_data[7:0];
      2'b01: selected_byte = wide_data[15:8];
      2'b10: selected_byte = wide_data[23:16];
      default: selected_byte = wide_data[31:24];
    endcase
  end
endmodule
module Comb_IfElse (
  input wire condition,
  input wire [15:0] value1,
  input wire [15:0] value2,
  output reg [15:0] result_val
);
  always_comb begin
    if (condition) begin
      result_val = value1;
    end else begin
      result_val = value2;
    end
  end
endmodule
class MySimpleClass;
  int data;
  function new(int val);
    data = val;
  endfunction
  function int getData();
    return data;
  endfunction
endclass
module Class_Usage (
  input wire trigger_in,
  output reg status_out
);
  function automatic int instantiate_and_use_class(input int val);
    MySimpleClass obj = new(val);
    return obj.getData();
  endfunction
  always_comb begin
    int temp_val;
    if (trigger_in) begin
      temp_val = instantiate_and_use_class(100);
    end else begin
      temp_val = instantiate_and_use_class(200);
    end
    status_out = (temp_val == 100) || (temp_val == 200);
  end
endmodule

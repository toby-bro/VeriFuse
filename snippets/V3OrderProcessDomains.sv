module SequentialLogic (
  input logic clk,
  input logic rst,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  logic [7:0] internal_reg;
  always @(posedge clk or negedge rst) begin
    if (~rst) begin
      internal_reg <= 8'h00;
    end else begin
      internal_reg <= data_in;
    end
  end
  assign data_out = internal_reg;
endmodule
module CombinationalLogicImplicit (
  input logic [3:0] a,
  input logic [3:0] b,
  output logic [3:0] sum
);
  always @* begin
    sum = a + b;
  end
endmodule
module CombinationalLogicExplicit (
  input logic sel,
  input logic [15:0] data0,
  input logic [15:0] data1,
  output logic [15:0] data_out
);
  always @(sel or data0 or data1) begin
    if (sel) begin
      data_out = data1;
    end else begin
      data_out = data0;
    end
  end
endmodule
module MixedLogic (
  input logic clk,
  input logic async_reset,
  input logic seq_in,
  input logic comb_in1,
  input logic comb_in2,
  output logic seq_out,
  output logic comb_out
);
  logic seq_reg;
  logic comb_intermediate;
  always @(posedge clk or negedge async_reset) begin
    if (!async_reset) begin
      seq_reg <= 1'b0;
    end else begin
      seq_reg <= seq_in;
    end
  end
  assign seq_out = seq_reg;
  always @(seq_reg or comb_in1 or comb_in2) begin
    comb_intermediate = (seq_reg & comb_in1) | (~seq_reg & comb_in2);
  end
  assign comb_out = comb_intermediate;
endmodule
module MultipleClockSensitivity (
    input logic clk_a,
    input logic clk_b,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic [7:0] data_combined
);
  logic [7:0] reg_a_q;
  logic [7:0] reg_b_q;
  always @(posedge clk_a or posedge clk_b) begin
      if (data_a > data_b) begin
          reg_a_q <= data_a;
          reg_b_q <= 8'h00;
      end else begin
          reg_a_q <= 8'h00;
          reg_b_q <= data_b;
      end
  end
  assign data_combined = reg_a_q | reg_b_q;
endmodule
module SimpleAssign (
    input logic [9:0] val_in,
    output logic [9:0] val_out
);
    assign val_out = val_in;
endmodule
module LogicDependencyChain (
    input logic d_in,
    input logic clk,
    output logic q_out
);
    logic q1, q2;
    always @(posedge clk) begin
        q1 <= d_in;
    end
    always @(q1) begin
        q2 = ~q1;
    end
    assign q_out = q2;
endmodule

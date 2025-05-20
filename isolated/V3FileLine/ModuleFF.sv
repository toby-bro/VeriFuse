module ModuleFF (
    input logic reset,
    input bit [3:0] in1,
    input bit [3:0] in2,
    output bit [3:0] out1,
    output bit [3:0] out2,
    input logic clk
);
    parameter int MAX_COUNT = 10;
      localparam int START_VAL = 5;
      logic [3:0] ff_reg;
      integer unused_int_var;
      always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      ff_reg <= START_VAL;
      out1 <= '0;
      out2 <= '0;
      unused_int_var <= 0;
    end else begin
      case ({in1, in2})
        8'h00: ff_reg <= ff_reg;
        8'h01: ff_reg <= in1 + in2;
        default: ff_reg <= MAX_COUNT;
      endcase
      out1 <= ff_reg;
      out2 <= {in1[0], in1[0], in1[0], in1[0]} | {in2[3], in2[2], in2[1], in2[0]};
    end
      end
endmodule


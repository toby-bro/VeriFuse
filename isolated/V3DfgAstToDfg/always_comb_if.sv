module always_comb_if (
    output logic [31:0] out,
    input logic [31:0] in1,
    input logic [31:0] in2,
    input logic cond
);
    always_comb begin
    if (cond) begin
      out = in1;
    end else begin
      out = in2;
    end
      end
endmodule


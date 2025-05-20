module timed_assign_unhandled (
    input logic [7:0] in,
    output logic [7:0] out,
    input logic clk
);
    always @(posedge clk) begin
    out <= in;
      end
endmodule


module CombinationalLogicImplicit (
    output logic [3:0] sum,
    input logic [3:0] a,
    input logic [3:0] b
);
    always @* begin
    sum = a + b;
      end
endmodule


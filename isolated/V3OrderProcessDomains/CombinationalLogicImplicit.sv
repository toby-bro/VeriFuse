module CombinationalLogicImplicit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [3:0] sum
);
    always @* begin
        sum = a + b;
    end
endmodule


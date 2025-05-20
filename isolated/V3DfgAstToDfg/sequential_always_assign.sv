module sequential_always_assign (
    output logic [7:0] out,
    input logic clk,
    input logic [7:0] in
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule


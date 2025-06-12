module ModClockedReg (
    input logic clk,
    input logic d,
    output logic q
);
    always @(posedge clk) begin
    q <= d;
    end
endmodule


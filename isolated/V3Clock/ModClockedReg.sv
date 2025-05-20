module ModClockedReg (
    output logic q,
    input logic clk,
    input logic d
);
    always @(posedge clk) begin
    q <= d;
    end
endmodule


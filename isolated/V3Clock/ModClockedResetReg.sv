module ModClockedResetReg (
    input logic clk,
    input logic rst_n,
    input logic d,
    output logic q
);
    always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        q <= 1'b0;
    end else begin
        q <= d;
    end
    end
endmodule


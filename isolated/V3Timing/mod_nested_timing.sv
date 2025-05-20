module mod_nested_timing (
    input logic condition,
    output logic out1,
    output logic out2,
    input logic clk
);
    always @(posedge clk) begin
    if (condition) begin
        #2 out1 <= 1'b1;
    end else begin
        @(negedge clk);
        out2 <= 1'b1;
    end
    end
endmodule


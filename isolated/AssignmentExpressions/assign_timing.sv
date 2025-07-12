module assign_timing (
    input logic clk,
    input logic in_a,
    input logic in_b,
    input logic rst_n,
    output logic out_blocking_timing,
    output logic out_non_blocking_timing
);
    logic reg_blocking;
    logic reg_non_blocking;
    always @(posedge clk) begin
        reg_blocking = @(negedge clk) in_a;
        reg_non_blocking <= @(posedge clk) in_b;
    end
    assign out_blocking_timing = reg_blocking;
    assign out_non_blocking_timing = reg_non_blocking;
endmodule


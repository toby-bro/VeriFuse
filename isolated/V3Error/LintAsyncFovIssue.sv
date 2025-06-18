module LintAsyncFovIssue (
    input logic clk,
    input logic in_h,
    input logic rst_n,
    output logic out_i
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_i <= 1'b0;
        end else begin
            out_i <= in_h & out_i;
        end
    end
endmodule


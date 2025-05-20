module LintAsyncFovIssue (
    input logic rst_n,
    input logic in_h,
    output logic out_i,
    input logic clk
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_i <= 1'b0;
        end else begin
            out_i <= in_h & out_i;
        end
    end
endmodule


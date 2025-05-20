module LintSeqNonBlockAssign (
    input logic clk,
    input logic in_f,
    output logic out_g
);
    always_ff @(posedge clk) begin
        out_g <= in_f;
    end
endmodule


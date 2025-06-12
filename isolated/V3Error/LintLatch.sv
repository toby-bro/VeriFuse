module LintLatch (
    output logic out_l,
    input logic in_j,
    input logic in_k
);
    always_comb begin
        if (in_j) begin
            out_l = in_k;
        end else begin
            out_l = 1'b0; 
        end
    end
endmodule


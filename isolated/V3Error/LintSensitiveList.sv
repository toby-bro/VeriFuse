module LintSensitiveList (
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule


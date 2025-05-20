module LintSensitiveList (
    input logic in_q,
    output logic out_r,
    input logic in_p
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule


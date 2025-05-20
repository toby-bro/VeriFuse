module LintCombBlockAssign (
    input logic in_c,
    input logic in_d,
    output logic out_e
);
    always_comb begin
        out_e = in_c & in_d;
    end
endmodule


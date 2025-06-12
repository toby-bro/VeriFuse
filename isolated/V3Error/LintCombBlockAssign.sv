module LintCombBlockAssign (
    output logic out_e,
    input logic in_c,
    input logic in_d
);
    always_comb begin
        out_e = in_c & in_d;
    end
endmodule


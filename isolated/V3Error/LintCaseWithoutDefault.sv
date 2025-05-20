module LintCaseWithoutDefault (
    input logic [1:0] in_sel,
    input logic in_val,
    output logic out_reg
);
    always_comb begin
        case (in_sel)
            2'b00: out_reg = in_val;
            2'b01: out_reg = ~in_val;
            2'b10: out_reg = in_val;
        endcase
    end
endmodule


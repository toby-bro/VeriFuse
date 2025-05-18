module LintUnusedSignal(
    input logic in_a,
    output logic out_b
);
    logic unused_w; 
    assign out_b = in_a;
endmodule
module LintImplicitWidth(
    input logic [7:0] in_wide,
    output logic [3:0] out_narrow
);
    assign out_narrow = in_wide;
endmodule
module LintCombBlockAssign(
    input logic in_c,
    input logic in_d,
    output logic out_e
);
    always_comb begin
        out_e = in_c & in_d;
    end
endmodule
module LintSeqNonBlockAssign(
    input logic clk,
    input logic in_f,
    output logic out_g
);
    always_ff @(posedge clk) begin
        out_g <= in_f;
    end
endmodule
module LintCaseWithoutDefault(
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
module LintAsyncFovIssue(
    input logic clk,
    input logic rst_n,
    input logic in_h,
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
module LintLatch(
    input logic in_j,
    input logic in_k,
    output logic out_l
);
    always_comb begin
        if (in_j) begin
            out_l = in_k;
        end else begin
            out_l = 1'b0; 
        end
    end
endmodule
module LintParamUnused #(parameter UNUSED_PARAM = 8) (
    input logic in_m,
    output logic out_n
);
    assign out_n = in_m;
endmodule
module LintSensitiveList(
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
endmodule

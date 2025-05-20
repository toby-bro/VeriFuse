module LintUnusedSignal (
    input logic in_a,
    output logic out_b
);
    logic unused_w; 
    assign out_b = in_a;
endmodule


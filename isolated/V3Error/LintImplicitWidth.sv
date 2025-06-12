module LintImplicitWidth (
    output logic [3:0] out_narrow,
    input logic [7:0] in_wide
);
    assign out_narrow = in_wide;
endmodule


module expr_postsub_comb (
    input logic [7:0] in_val_m2,
    input logic [7:0] sub_val_m2,
    output logic [7:0] out_diff_m2,
    output logic [7:0] var_out_m2
);
    logic [7:0] var_m2;
    
    assign var_m2 = in_val_m2;
    assign out_diff_m2 = (var_m2--) - sub_val_m2;
    assign var_out_m2 = var_m2;
endmodule

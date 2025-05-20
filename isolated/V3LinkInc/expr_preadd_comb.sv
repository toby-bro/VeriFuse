module expr_preadd_comb (
    input logic [7:0] in_val_m1,
    input logic [7:0] add_val_m1,
    output logic [7:0] out_sum_m1,
    output logic [7:0] var_out_m1
);
    logic [7:0] var_m1;
      always_comb begin
    var_m1 = in_val_m1;
    out_sum_m1 = (++var_m1) + add_val_m1;
    var_out_m1 = var_m1;
      end
endmodule


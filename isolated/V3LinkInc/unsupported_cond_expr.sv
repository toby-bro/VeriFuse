module unsupported_cond_expr (
    input logic [7:0] in_val_m10,
    input bit condition_m10,
    output logic [7:0] out_val_m10
);
    logic [7:0] var_m10;
      always_comb begin
    var_m10 = in_val_m10;
    out_val_m10 = condition_m10 ? var_m10 : var_m10;
    var_m10++;
      end
endmodule


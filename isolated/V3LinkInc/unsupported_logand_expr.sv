module unsupported_logand_expr (
    input logic [7:0] in_a_m9,
    input logic [7:0] in_b_m9,
    output logic out_m9
);
    logic [7:0] var_m9;
      always_comb begin
    var_m9 = in_a_m9;
    if ((var_m9 > 10) && (in_b_m9 < 5)) begin
      out_m9 = 1;
    end else begin
      out_m9 = 0;
    end
    var_m9++;
      end
endmodule


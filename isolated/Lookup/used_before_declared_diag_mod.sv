module used_before_declared_diag_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    logic [7:0] undeclared_var_ubddm = 8'd5;
    assign out_val = in_val + undeclared_var_ubddm;
endmodule


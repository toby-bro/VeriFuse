module ModuleLineDirective (
    input logic in1,
    output logic out1
);
    logic internal_sig_a;
      logic internal_sig_b;
      logic unused_line_var;
    `line 100 "virtual_file_A.sv" 1
      assign internal_sig_a = in1;
    `line 20 "virtual_file_B.sv" 1
      assign internal_sig_b = ~internal_sig_a;
      assign unused_line_var = 1'b1;
    `line 150 "virtual_file_A.sv" 2
      assign out1 = internal_sig_b;
    `line 1 "original_file.sv" 0
endmodule


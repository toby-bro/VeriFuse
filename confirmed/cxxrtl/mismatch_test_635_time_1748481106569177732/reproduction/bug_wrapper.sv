module bug_wrapper (
    output logic [6:0] reg_out,
    output logic clk_out
);
    bug dut();
    assign reg_out = dut.reg_bug;
    assign clk_out = dut.clk;
endmodule

module ansi_basic (
    input logic clk,
    output logic reset_n
);
    always_comb begin
        reset_n = clk;
    end
endmodule


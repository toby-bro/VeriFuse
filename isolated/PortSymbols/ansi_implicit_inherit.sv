module ansi_implicit_inherit (
    input logic [2:0] in1,
    input logic in2,
    output logic extra_out,
    output logic out1,
    output logic out2
);
    always_comb begin
        out1 = |in1;
        out2 = |in2;
        extra_out = out1 ^ out2;
    end
endmodule


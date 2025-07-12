module GenerateIfParam #(
    parameter bit GEN = 1
) (
    input logic sig_in,
    output logic sig_out
);
    generate
        if (GEN) begin : g_true
            assign sig_out = sig_in;
        end
        else begin : g_false
            assign sig_out = ~sig_in;
        end
    endgenerate
endmodule


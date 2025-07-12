module cu_timeunit_mod (
    input logic clk,
    output logic reset
);
    logic internal_sig;
    always_ff @(posedge clk) begin
        reset <= 1'b0;
        internal_sig = clk;
    end
endmodule


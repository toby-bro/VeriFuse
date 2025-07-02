module procedural_assert_mod (
    input logic clk,
    input logic [3:0] counter,
    input logic enable,
    input logic overflow,
    input logic reset_n,
    output logic proc_assert_out
);
    always @(posedge clk) begin
        if (reset_n) begin
            assert (!(!overflow && enable) || (counter <= 4'hE)) 
                else $error("Counter exceeded limit without overflow flag: %d", counter);
            assert (!(counter == 4'hF) || overflow) 
                else $warning("Counter at maximum but overflow not set");
            assert (!overflow || !enable)
                else $error("Enable still high during overflow");
        end
    end
    always @(posedge clk) begin
        assert (reset_n || (counter == 4'h0 && !overflow))
            else $error("Improper reset behavior");
    end
    property p_overflow_recovery;
        @(posedge clk) disable iff (!reset_n)
        $rose(overflow) |-> ##1 (counter == 4'h0) or ##2 (counter == 4'h0);
    endproperty
    assert property (p_overflow_recovery)
        else $error("Counter did not reset after overflow");
    assign proc_assert_out = enable && !overflow;
endmodule


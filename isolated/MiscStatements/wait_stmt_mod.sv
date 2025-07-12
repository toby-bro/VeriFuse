module wait_stmt_mod (
    input logic clk,
    input logic [1:0] state,
    output logic triggered
);
    static logic internal_trigger = 0;
    always @(posedge clk) begin
        wait (state == 2'b10) internal_trigger = 1;
    end
    assign triggered = internal_trigger;
endmodule


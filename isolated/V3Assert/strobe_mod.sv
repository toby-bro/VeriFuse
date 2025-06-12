module strobe_mod (
    input logic trigger_strobe,
    output logic strobe_out
);
    always @(trigger_strobe) begin
        if (trigger_strobe) begin
            $strobe("This is a strobe message");
        end
    end
    assign strobe_out = trigger_strobe;
endmodule


module monitoroff_mod (
    input logic trigger_monoff,
    output logic monoff_out
);
    always @(trigger_monoff) begin
        if (trigger_monoff) begin
            $monitoroff;
        end
    end
    assign monoff_out = trigger_monoff;
endmodule


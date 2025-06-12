module monitoroff_mod (
    output logic monoff_out,
    input logic trigger_monoff
);
    always @(trigger_monoff) begin
        if (trigger_monoff) begin
            $monitoroff;
        end
    end
    assign monoff_out = trigger_monoff;
endmodule


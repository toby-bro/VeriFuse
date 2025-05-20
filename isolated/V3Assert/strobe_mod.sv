module strobe_mod (
    output logic strobe_out,
    input logic trigger_strobe
);
    always @(trigger_strobe) begin
    if (trigger_strobe) begin
      $strobe("This is a strobe message");
    end
      end
      assign strobe_out = trigger_strobe;
endmodule


module PragmaOnceDirective (
    input bit trigger_input,
    output bit trigger_output
);
assign trigger_output = trigger_input;
endmodule


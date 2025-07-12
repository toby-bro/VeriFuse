module PragmaDiagnosticDirective (
    input int diag_input_val,
    output bit diag_output_flag
);
`ifdef SLANG_PRAGMA
`diagnostic push
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore "SLANG_UNUSED_VARIABLE"
`endif
`ifdef SLANG_PRAGMA
`diagnostic warn "SLANG_IMPLICIT_CAST"
`endif
`ifdef SLANG_PRAGMA
`diagnostic error "SLANG_MULTIPLE_DRIVER"
`endif
`ifdef SLANG_PRAGMA
`diagnostic fatal "SLANG_SYNTAX_ERROR_FATAL"
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore (value=("SLANG_UNDRIVEN_SIGNAL", "SLANG_UNREAD_SIGNAL"))
`endif
`ifdef SLANG_PRAGMA
`diagnostic warn (value="SLANG_LATCH_INFERRED")
`endif
assign diag_output_flag = (diag_input_val > 0);
`ifdef SLANG_PRAGMA
`diagnostic pop
`endif
endmodule


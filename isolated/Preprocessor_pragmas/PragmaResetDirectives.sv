module PragmaResetDirectives (
    input bit reset_request,
    output bit system_status_clear
);
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
assign system_status_clear = reset_request;
endmodule


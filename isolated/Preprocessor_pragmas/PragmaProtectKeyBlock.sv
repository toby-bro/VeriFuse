module PragmaProtectKeyBlock (
    input bit enable_crypto,
    output bit crypto_active
);
`ifdef SLANG_PRAGMA
`protect key
`endif
`ifdef SLANG_PRAGMA
`protect block
`endif
assign crypto_active = enable_crypto;
endmodule


module macro_stringification_user (
    input logic sel,
    output string str_out
);
    `define TO_STR(x) `"x`"
    `define TOKEN_NAME example_token
    localparam string S0 = `TO_STR(hello);
    localparam string S1 = `TO_STR(world_123);
    localparam string S2 = `TO_STR(`TOKEN_NAME);
    assign str_out = sel ? S0 : (sel ? S1 : S2);
endmodule


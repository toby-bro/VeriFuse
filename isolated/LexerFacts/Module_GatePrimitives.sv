module Module_GatePrimitives (
    input wire g_ctrl_n,
    input wire g_ctrl_p,
    input wire g_in,
    output wire g_out_and,
    output wire g_out_or
);
    and a1 (g_out_and, g_in, g_in);
    or  o1 (g_out_or , g_in, g_in);
endmodule


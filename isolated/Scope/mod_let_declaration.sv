module mod_let_declaration (
    input int in_val,
    output int out_val
);
    let my_let_expr = in_val + 5;
    assign out_val = my_let_expr * 2;
endmodule


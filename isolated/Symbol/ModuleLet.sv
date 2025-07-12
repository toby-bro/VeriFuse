module ModuleLet (
    input int a_in,
    input int b_in,
    output int c_out
);
    let my_add (x, y) = x + y;
    assign c_out = my_add(a_in, b_in);
endmodule


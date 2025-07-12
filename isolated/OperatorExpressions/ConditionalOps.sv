module ConditionalOps (
    input logic sel,
    input int val_false,
    input int val_true,
    output int out_val
);
    assign out_val = sel ? val_true : val_false;
endmodule


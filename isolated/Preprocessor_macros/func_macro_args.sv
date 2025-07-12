module func_macro_args (
    input int input_int,
    output int output_int
);
    `define ADD(a, b)       ((a) + (b))
    `define SUBTRACT(x, y)  ((x) - (y))
    localparam int P1_ADD = `ADD(10, 20);
    int p2_sub_var;
    always_comb begin
        p2_sub_var = `SUBTRACT(50, input_int);
    end
    assign output_int = P1_ADD + p2_sub_var;
endmodule


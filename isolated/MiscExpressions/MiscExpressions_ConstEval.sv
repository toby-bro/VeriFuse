module MiscExpressions_ConstEval (
    input int in_dummy,
    output int out_size
);
    class MyType;
        int x;
    endclass
    parameter type T = MyType;
    parameter int SIZE_OF_T = $bits(T); 
    assign out_size = SIZE_OF_T;
endmodule


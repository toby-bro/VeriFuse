module Module_ProceduralCode (
    input int in1,
    input int in2,
    output int add_out
);
    function automatic int add_func(input int a, b);
        return a + b;
    endfunction
    assign add_out = add_func(in1, in2);
endmodule


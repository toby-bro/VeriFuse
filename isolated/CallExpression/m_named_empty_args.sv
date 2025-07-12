module m_named_empty_args (
    input int in1,
    input int in2,
    input int in3,
    output int out_empty_default,
    output int out_named
);
    function automatic int complex_args(input int p1, input int p2 = 10, input int p3 = 20);
        return p1 + p2 + p3;
    endfunction
    initial begin
        out_named = complex_args(.p3(in3), .p1(in1), .p2(in2));
        out_empty_default = complex_args(in1, , in3);
    end
endmodule


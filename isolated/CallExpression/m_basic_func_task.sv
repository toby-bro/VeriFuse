module m_basic_func_task (
    input int in_a,
    input int in_b,
    output int out_default_func,
    output logic out_logic_func,
    output int out_sum_func
);
    function automatic int add_func(input int x, input int y = 5);
        return x + y;
    endfunction
    function automatic logic gt_func(input int a, input int b);
        return a > b;
    endfunction
    task automatic simple_task(input int val);
    endtask
    initial begin
        out_sum_func = add_func(in_a, in_b);
        out_logic_func = gt_func(in_a, in_b);
        out_default_func = add_func(in_a);
        simple_task(in_a);
    end
endmodule


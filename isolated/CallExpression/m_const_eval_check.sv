module m_const_eval_check (
    input int unused_in,
    output int unused_out
);
    parameter int param_val = get_const_val(5);
    function automatic int get_const_val(input int val);
        return val + 1;
    endfunction
    task automatic non_const_task(input int val);
    endtask
    function automatic void void_func(input int val);
    endfunction
    function automatic int func_with_output(output int out_val);
        out_val = 1;
        return 0;
    endfunction
    int dummy_out;
    assign unused_out = unused_in;
endmodule


module module_func (
    input int i_val1,
    input int i_val2,
    output int o_sum_doubled
);
    function automatic int add_and_double_func(input int input_val);
        int func_local_var;
        func_local_var = input_val + 1;
        return func_local_var * 2;
    endfunction
    assign o_sum_doubled = add_and_double_func(i_val1) + i_val2;
endmodule


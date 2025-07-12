module m_output_arg_check (
    input int data_in,
    output int output_from_func
);
    function automatic void func_with_output(output int out_val);
        out_val = data_in + 1;
    endfunction
    initial begin
        func_with_output(output_from_func);
    end
endmodule


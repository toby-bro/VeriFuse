module ref_args (
    input int add_val,
    input int value_in,
    output int const_ref_val_out,
    output int value_out
);
    function automatic int modify_ref_func(ref int x, input int increment);
        x = x + increment;
        return x;
    endfunction
    task automatic read_const_ref(const ref int y, output int out);
        out = y * 2;
    endtask
    int temp_val;
    int const_ref_temp;
    always_comb begin
        temp_val = value_in;
        value_out = modify_ref_func(temp_val, add_val);
        const_ref_temp = value_in + 1;
        read_const_ref(const_ref_temp, const_ref_val_out);
    end
endmodule


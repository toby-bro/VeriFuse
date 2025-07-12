module module_subroutine_return (
    input int in_a,
    input int in_b,
    input bit in_cond,
    output int out_add_result,
    output bit out_is_even
);
    function automatic int add_values(int val1, int val2);
        int temp = val1 + val2;
        if (temp > 100)
            return 100;
        return temp;
    endfunction
    task automatic check_even(input int value, output bit is_even);
        if ((value % 2) == 0) begin
            is_even = 1;
            return;
        end
        is_even = 0;
    endtask
    always_comb begin
        out_add_result = add_values(in_a, in_b);
        check_even(out_add_result, out_is_even);
    end
endmodule


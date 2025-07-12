module ModuleSubroutines (
    input int in1,
    input int in2,
    output int out_func,
    output int out_task
);
    function automatic int add_func (input int a, input int b);
        return a + b;
    endfunction
    task automatic multiply_task (input int a, input int b, output int result);
        result = a * b;
    endtask
    assign out_func = add_func(in1, in2);
    always_comb begin
        int temp_res;
        multiply_task(in1, in2, temp_res);
        out_task = temp_res;
    end
endmodule


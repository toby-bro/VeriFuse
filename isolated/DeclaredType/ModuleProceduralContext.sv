module ModuleProceduralContext (
    input int in_proc,
    output logic [7:0] out_func_var,
    output int out_proc,
    output int out_task_var
);
    int task_var_output;
    logic [7:0] func_var_output;
    task my_task(input int arg1);
        automatic int task_var = arg1 * 2;
        task_var_output = task_var;
    endtask
    function int my_function(input [7:0] implicit_arg);
        automatic logic [7:0] func_var = implicit_arg + 1;
        func_var_output = func_var;
        return func_var;
    endfunction
    int func_result;
    always_comb begin
        func_result = my_function(in_proc);
        my_task(in_proc + 10);
    end
    assign out_proc = func_result;
    assign out_task_var = task_var_output;
    assign out_func_var = func_var_output;
endmodule


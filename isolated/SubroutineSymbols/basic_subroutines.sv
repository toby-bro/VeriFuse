module basic_subroutines (
    input int data_in,
    input logic enable,
    output int simple_func_result,
    output logic simple_task_done
);
    function automatic int simple_func(input int a, input int b);
        return a + b;
    endfunction
    task automatic simple_task(input int data, output logic done);
        done = (data > 0);
    endtask
    always_comb begin
        simple_func_result = 0;
        simple_task_done = 1'b0;
        if (enable) begin
            simple_func_result = simple_func(data_in, 10);
            simple_task(data_in, simple_task_done);
        end else begin
            simple_func_result = simple_func(data_in, 5);
            simple_task(0, simple_task_done);
        end
    end
endmodule


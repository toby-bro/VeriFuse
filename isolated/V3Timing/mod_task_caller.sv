module mod_task_caller (
    input logic clk,
    input logic rst,
    input logic task_in,
    output logic task_out
);
    initial begin
    task_out = 1'b0;
    timed_task(task_in, task_out);
    end
endmodule


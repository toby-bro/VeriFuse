module module_return_task_automatic (
    output logic [7:0] out_data,
    input logic [7:0] in_data
);
    task automatic my_task (input logic [7:0] value, output logic [7:0] result);
        logic [7:0] temp;
        temp = value + 1;
        if (temp > 10) begin
            result = 8'b0;
            return;
        end
        result = temp;
    endtask
    always_comb begin: task_call_block
        logic [7:0] task_result;
        my_task(in_data, task_result);
        out_data = task_result;
    end
endmodule


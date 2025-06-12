module task_example (
    output logic task_out,
    input logic task_in
);
    task automatic process_data (input logic data);
        logic temp;
        temp = data; 
    endtask 
    assign task_out = task_in;
endmodule


module task_example (
    input logic task_in,
    output logic task_out
);
    task automatic process_data (input logic data);
    logic temp;
    temp = data; 
      endtask 
      assign task_out = task_in;
endmodule


module mod_always_delay (
    input logic clk,
    input logic rst,
    output logic out
);
always @(posedge clk or negedge rst) begin
    if (!rst) begin
        out <= 1'b0;
    end else begin
        #5 out <= ~out;
    end
end
endmodule
module mod_always_event (
    input logic clk,
    input logic rst,
    input logic in,
    output logic out
);
always @(posedge clk or negedge rst) begin
    if (!rst) begin
        out <= 1'b0;
    end else begin
        out <= in;
    end
end
endmodule
module mod_initial_wait (
    input logic start,
    input logic condition,
    output logic done
);
initial begin
    done = 1'b0;
    wait(start);
    wait(condition);
    done = 1'b1;
end
endmodule
task timed_task (
    input logic task_in,
    output logic task_out
);
    #3 task_out = task_in;
    @(posedge task_in);
    task_out = ~task_out;
endtask
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
function logic simple_func(input logic func_in);
    return ~func_in;
endfunction
function logic func_caller(input logic func_in);
    logic temp_out;
    temp_out = simple_func(func_in);
    return temp_out;
endfunction
module mod_func_caller (
    input logic func_in,
    output logic func_out
);
    initial begin
        func_out = func_caller(func_in);
    end
endmodule
module mod_fork_join (
    input logic start,
    input logic in1,
    input logic in2,
    output logic out
);
initial begin
    out = 1'b0;
    wait(start);
    fork
        begin : branch1
            #2 out = in1;
        end
        begin : branch2
            @(posedge in2);
            out = in2;
        end
    join
    out = out + 1;
end
endmodule
module mod_fork_none_disable (
    input logic start,
    input logic enable,
    output logic out1,
    output logic out2,
    output logic out_done
);
initial begin
    out1 = 1'b0;
    out2 = 1'b0;
    out_done = 1'b0;
    wait(start);
    fork : my_fork
        begin : branch_a
            #5 out1 = 1'b1;
        end
        begin : branch_b
            @(posedge enable);
            if (!enable) disable fork;
            else out2 = 1'b1;
        end
    join_none
    out_done = 1'b1;
end
endmodule
module mod_wait_fork (
    input logic start,
    input logic trigger,
    output logic out
);
initial begin
    out = 1'b0;
    wait(start);
    fork : my_async_fork
        begin : async_branch
            #10 out = 1'b1;
        end
    join_none
    wait(trigger);
    wait fork;
    out = out + 1;
end
endmodule
module mod_assign_delay (
    input logic in,
    output logic out
);
assign #3 out = in;
endmodule
module mod_nested_timing (
    input logic clk,
    input logic condition,
    output logic out1,
    output logic out2
);
always @(posedge clk) begin
    if (condition) begin
        #2 out1 <= 1'b1;
    end else begin
        @(negedge clk);
        out2 <= 1'b1;
    end
end
endmodule

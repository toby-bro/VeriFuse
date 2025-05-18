module ModuleReturn (
    input int in1,
    output int out1
);
    int internal_var1;
    function automatic int func_return(int val);
        int func_local_var;
        func_local_var = val + 1;
        if (val > 10) begin
            return func_local_var + 4;
        end else begin
            return func_local_var - 3;
        end
    endfunction
    task automatic task_return(int val);
        int task_local_var;
        task_local_var = val * 3;
        if (val < 0) begin
            return;
        end
        internal_var1 = task_local_var;
        if (val > 100) begin
            return;
        end
        internal_var1 = internal_var1 + 1;
    endtask
    always @* begin
        internal_var1 = 0;
        out1 = func_return(in1);
        task_return(in1 - 5);
    end
endmodule
module ModuleLoopBreak (
    input int in2,
    output int out2
);
    int i;
    int temp2;
    logic [7:0] data_array [0:7];
    always @* begin
        temp2 = 0;
        data_array = '{default: 0};
        if (in2 >= 0 && in2 < 8) data_array[in2] = 1;
        i = 0;
        while (i < 10) begin
            if (i == in2) begin
                break;
            end
            temp2 = temp2 + 1;
            i = i + 1;
        end
        for (i=0; i<10; i=i+1) begin
            if (i == in2 + 1) begin
                break;
            end
            temp2 = temp2 + 2;
        end
        repeat (in2 > 0 && in2 < 6 ? in2 : 3) begin : repeat_break_block
            if (temp2 > 50) begin
                break;
            end
            temp2 = temp2 + 3;
        end
        foreach (data_array[idx]) begin
            if (data_array[idx] == 1) begin
                break;
            end
            temp2 = temp2 + 4;
        end
        out2 = temp2;
    end
endmodule
module ModuleLoopContinue (
    input int in3,
    output int out3
);
    int i;
    int temp3;
    logic [7:0] data_array [0:7];
    always @* begin
        temp3 = 0;
        data_array = '{default: 0};
        if (in3 >= 0 && in3 < 8) data_array[in3] = 1;
        i = 0;
        while (i < 10) begin
            if (i == in3) begin
                i = i + 1;
                continue;
            end
            temp3 = temp3 + 1;
            i = i + 1;
        end
        for (i=0; i<10; i=i+1) begin
            if (i == in3 + 1) begin
                continue;
            end
            temp3 = temp3 + 2;
        end
        repeat (in3 > 0 && in3 < 6 ? in3 : 3) begin : repeat_cont_block
            if (temp3 > 30 && temp3 < 40) begin
                continue;
            end
            temp3 = temp3 + 3;
        end
        foreach (data_array[idx]) begin
            if (data_array[idx] == 1) begin
                continue;
            end
            temp3 = temp3 + 4;
        end
        out3 = temp3;
    end
endmodule
module ModuleDisableSimple (
    input bit in4_simple,
    output logic out4_simple
);
    logic temp4_simple;
    always @* begin
        temp4_simple = 0;
        named_block_simple: begin
            if (in4_simple) begin
                temp4_simple = 1;
                disable named_block_simple;
            end
            temp4_simple = temp4_simple + 2;
        end
        out4_simple = temp4_simple;
    end
endmodule
module ModuleRepeatLoop (
    input int in5,
    output int out5
);
    int temp5;
    always @* begin
        temp5 = 0;
        repeat (5) begin
            temp5 = temp5 + 1;
        end
        out5 = temp5;
    end
endmodule
module ModuleDoWhile (
    input bit in6,
    output logic out6
);
    logic temp6;
    int counter6;
    always @* begin
        temp6 = 0;
        counter6 = 0;
        do begin
            temp6 = ~temp6;
            counter6 = counter6 + 1;
        end while (in6 && counter6 < 3);
        out6 = temp6;
    end
endmodule
module ModulePragma (
    input int in7,
    output int out7
);
    int i;
    int temp7;
    always @* begin
        temp7 = 0;
        (* verilator unroll_disable *)
        for (i = 0; i < 5; i = i + 1) begin
            temp7 = temp7 + 1;
        end
        (* verilator unroll_full *)
        while (temp7 < 10) begin
             temp7 = temp7 + 1;
        end
        out7 = temp7;
    end
endmodule
module ModuleFork (
    input bit in8,
    output logic out8
);
    logic temp8a, temp8b;
    always @* begin
        temp8a = 0;
        temp8b = 0;
        fork
            begin
                temp8a = in8;
            end
            begin
                temp8b = ~in8;
            end
        join
        out8 = temp8a ^ temp8b;
    end
endmodule
module ModuleDisableForkWarn (
    input bit in9,
    output logic out9
);
    logic temp9;
    always @* begin
        temp9 = 0;
        outer_control: begin
            if (in9) begin
                disable block_with_fork_and_disable;
            end
            block_with_fork_and_disable: begin
                fork
                    begin temp9 = temp9 + 4; end
                    begin temp9 = temp9 + 8; end
                join
                temp9 = temp9 + 16;
            end 
            temp9 = temp9 + 32; 
        end 
        temp9 = temp9 + 64;
        out9 = temp9;
    end
endmodule
module ModuleReturnFork (
    input bit in10,
    output logic out10
);
    logic temp10;
    task automatic task_with_return_in_fork;
        if (in10) begin
            temp10 = 5;
            return; 
        end
        temp10 = 1;
    endtask
    always @* begin
        temp10 = 0;
        fork
            begin
                task_with_return_in_fork();
                temp10 = temp10 + 2; 
            end
            begin
                if (!in10) temp10 = temp10 + 10;
            end
        join
        out10 = temp10;
    end
endmodule
module ModuleDisableNested (
    input bit in14,
    output logic out14
);
    logic temp14;
    always @* begin
        temp14 = 0;
        nested_level1: begin
           nested_level2: begin
              if (in14) begin
                 temp14 = 1;
                 disable nested_level1; 
              end
           end
        end
        temp14 = temp14 + 2; 
        out14 = temp14;
    end
endmodule

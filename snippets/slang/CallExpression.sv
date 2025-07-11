module m_basic_func_task (
    input int in_a,
    input int in_b,
    output int out_sum_func,
    output logic out_logic_func,
    output int out_default_func
);
    function automatic int add_func(input int x, input int y = 5);
        return x + y;
    endfunction
    function automatic logic gt_func(input int a, input int b);
        return a > b;
    endfunction
    task automatic simple_task(input int val);
    endtask
    initial begin
        out_sum_func = add_func(in_a, in_b);
        out_logic_func = gt_func(in_a, in_b);
        out_default_func = add_func(in_a);
        simple_task(in_a);
    end
endmodule
module m_named_empty_args (
    input int in1,
    input int in2,
    input int in3,
    output int out_named,
    output int out_empty_default
);
    function automatic int complex_args(input int p1, input int p2 = 10, input int p3 = 20);
        return p1 + p2 + p3;
    endfunction
    initial begin
        out_named = complex_args(.p3(in3), .p1(in1), .p2(in2));
        out_empty_default = complex_args(in1, , in3);
    end
endmodule
module m_system_funcs (
    input int in_val,
    input bit [31:0] in_packed,
    input int unpacked_array_input [4],
    output int out_clog2,
    output longint out_time,
    output int out_unpacked_size
);
    initial begin
        out_clog2 = $clog2(in_val + 1);
        out_time = $time;
        out_unpacked_size = $size(unpacked_array_input);
    end
endmodule
module m_array_methods (
    input int unused_in,
    input int init_val,
    output int size_out,
    output int sum_out,
    output int min_out,
    output int push_back_val
);
    int my_queue [$];
    initial begin
        my_queue = '{1, 5, 2, 8, 3};
        size_out = my_queue.size();
        sum_out = my_queue.sum();
        if (my_queue.size() != 0) begin
            min_out = my_queue.min()[0];
        end else begin
            min_out = 0;
        end
        my_queue.sort();
        my_queue.push_back(init_val);
        push_back_val = my_queue[$];
    end
endmodule
module m_array_methods_with (
    input int threshold,
    input int init_data [10],
    output int first_index_gt_threshold,
    output int unique_count,
    output int first_value_gt_threshold
);
    int data_queue [$];
    initial begin
        foreach(init_data[i]) begin
            data_queue.push_back(init_data[i]);
        end
        begin
            static int found_indices[] = data_queue.find_index with ( item > threshold );
            if (found_indices.size() != 0) begin
                 first_index_gt_threshold = found_indices[0];
                 first_value_gt_threshold = data_queue[found_indices[0]];
            end else begin
                 first_index_gt_threshold = -1;
                 first_value_gt_threshold = -1;
            end
        end
        unique_count = data_queue.unique().size();
    end
endmodule
module m_class_methods (
    input int initial_val,
    output int static_result,
    output int instance_result,
    output int new_instance_result
);
    class MyClass;
        int instance_var;
        static function automatic int static_method(input int val);
            return val * 2;
        endfunction
        function automatic int instance_method(input int val);
            this.instance_var = val;
            return this.instance_var + 1;
        endfunction
        function new(input int val);
            instance_var = val;
        endfunction
    endclass
    MyClass instance1;
    MyClass instance2;
    initial begin
        static_result = MyClass::static_method(initial_val);
        instance1 = new(initial_val + 1);
        instance_result = instance1.instance_method(initial_val + 5);
        instance2 = new(initial_val + 10);
        new_instance_result = instance2.instance_method(initial_val + 15);
    end
endmodule
module m_randomize_method (
    input bit clk,
    input int seed_in,
    output bit [7:0] rand_byte_out,
    output int rand_int_out
);
    class RandClass;
        rand bit [7:0] byte_var;
        rand int int_var;
        constraint c_byte { byte_var > 10; }
        constraint c_int { int_var < 100; }
    endclass
    RandClass rand_instance;
    always @(posedge clk) begin
        if (rand_instance == null) begin
             rand_instance = new();
        end
        void'(rand_instance.randomize() with {
            byte_var inside {[20:50]};
            int_var > 10;
        });
        rand_byte_out = rand_instance.byte_var;
        rand_int_out = rand_instance.int_var;
    end
endmodule
module m_output_arg_check (
    input int data_in,
    output int output_from_func
);
    function automatic void func_with_output(output int out_val);
        out_val = data_in + 1;
    endfunction
    initial begin
        func_with_output(output_from_func);
    end
endmodule
module m_driver_check (
    input bit clk,
    input int val_in,
    output int driven_var
);
    int my_driven_var;
    function automatic void write_to_var(input int val);
        my_driven_var = val;
    endfunction
    always @(posedge clk) begin
        write_to_var(val_in);
    end
    assign driven_var = my_driven_var;
endmodule
module m_const_eval_check (
    input int unused_in,
    output int unused_out
);
    parameter int param_val = get_const_val(5);
    function automatic int get_const_val(input int val);
        return val + 1;
    endfunction
    task automatic non_const_task(input int val);
    endtask
    function automatic void void_func(input int val);
    endfunction
    function automatic int func_with_output(output int out_val);
         out_val = 1;
         return 0;
    endfunction
    int dummy_out;
    assign unused_out = unused_in;
endmodule

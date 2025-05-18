module module_basic_task_func (
    input logic [7:0] in_data_task,
    input logic [7:0] in_data_func,
    output logic [7:0] out_data_task,
    output logic [7:0] out_data_func
);
    task automatic process_task;
        input logic [7:0] data_in;
        output logic [7:0] data_out;
        data_out = data_in + 8'd5;
    endtask
    function automatic logic [7:0] process_func;
        input logic [7:0] data_in;
        return data_in * 8'd2;
    endfunction
    always_comb begin
        logic [7:0] task_temp;
        process_task(in_data_task, task_temp);
        out_data_task = task_temp;
        out_data_func = process_func(in_data_func);
    end
endmodule
module module_ports (
    input logic [3:0] in1,
    input logic [3:0] in2,
    output logic [7:0] out1,
    inout wire [3:0] inout1
);
    function automatic logic [7:0] calculate_ports;
        input logic [3:0] i_a;
        input logic [3:0] i_b;
        inout logic [3:0] io_val;
        io_val = io_val + 4'd1;
        return {i_a, i_b} + {4'b0, io_val};
    endfunction
    logic [3:0] inout1_reg;
    assign inout1 = inout1_reg;
    always_comb begin
        logic [7:0] func_result;
        logic [3:0] func_inout_val;
        inout1_reg = inout1;
        func_inout_val = inout1_reg;
        func_result = calculate_ports(
            .i_a(in1),
            .i_b(in2),
            .io_val(func_inout_val)
        );
        out1 = func_result;
        inout1_reg = func_inout_val;
    end
endmodule
module module_defaults (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    function automatic logic [7:0] add_with_default;
        input logic [7:0] a;
        input logic [7:0] b = 8'd10;
        input logic [7:0] c = 8'd20;
        return a + b + c;
    endfunction
    always_comb begin
        out_val = add_with_default(in_val, 8'd10, 8'd20); // Explicitly pass all arguments
    end
endmodule
module module_noinline (
    input logic [7:0] input_val,
    output logic [7:0] output_val
);
    (* no_inline *)
    task automatic process_noinline;
        input logic [7:0] data_in;
        output logic [7:0] data_out;
        data_out = data_in - 8'd3;
    endtask
    always_comb begin
        logic [7:0] task_temp;
        process_noinline(input_val, task_temp);
        output_val = task_temp;
    end
endmodule
module module_dpi (
    input logic [31:0] dpi_in,
    output logic [31:0] dpi_out
);
    (* pure *) import "DPI-C" function int dpi_add_one(int a);
    (* context *) import "DPI-C" function real dpi_get_time();
    export "DPI-C" task dpi_process_task;
    export "DPI-C" task dpi_get_string;
    logic [7:0] module_state;
    task automatic dpi_process_task;
        input int val;
        module_state = module_state + val;
    endtask
    task automatic dpi_get_string;
        input string in_s;
        output chandle out_ch;
    begin
        out_ch = 0;
    end
    endtask
    real current_time;
    chandle processed_string_handle;
    always_comb begin
        int result;
        result = dpi_add_one(dpi_in);
        dpi_out = result;
        current_time = dpi_get_time();
        dpi_get_string("hello", processed_string_handle);
        dpi_process_task(1);
    end
endmodule
module module_purity (
    input logic [7:0] p_in,
    output logic [7:0] p_out
);
    logic [7:0] module_var = 8'd100;
    function automatic logic [7:0] impure_func;
        input logic [7:0] local_in;
        return local_in + module_var;
    endfunction
    always_comb begin
        p_out = impure_func(p_in);
    end
endmodule
module module_class (
    input logic [7:0] class_in,
    output logic [7:0] class_out
);
    class MyClass;
        int value;
        function new(int initial_value);
            this.value = initial_value;
            this.value = this.value + 1;
        endfunction
        function automatic int add_to_value(int add_val);
            this.value = this.value + add_val;
            return this.value;
        endfunction
    endclass
    MyClass my_instance;
    int method_result;
    logic initialized = 1'b0;
    always_comb begin
        if (!initialized) begin
            my_instance = new(10);
            initialized = 1'b1;
        end
        method_result = my_instance.add_to_value(class_in);
        class_out = method_result;
    end
endmodule
module module_loops (
    input logic [7:0] loop_in,
    output logic [7:0] loop_out
);
    always_comb begin
        logic [7:0] temp_val = loop_in;
        int count = 0;
        while (count < 5 && temp_val < 200) begin
            temp_val = temp_val + 1;
            count = count + 1;
        end
        loop_out = temp_val;
    end
endmodule
module module_return (
    input logic [7:0] ret_in,
    output logic [7:0] ret_out
);
    function automatic logic [7:0] process_return;
        input logic [7:0] val;
        logic [7:0] temp = val + 5;
        return temp * 2;
    endfunction
    always_comb begin
        ret_out = process_return(ret_in);
    end
endmodule
module module_sensitivity (
    input logic sens_in_a,
    input logic sens_in_b,
    output logic sens_out
);
    function automatic logic dummy_func(logic val);
        return !val;
    endfunction
    always @(sens_in_a or sens_in_b) begin
        sens_out = sens_in_a ^ sens_in_b;
    end
endmodule
module module_dpi_arrays (
    input logic [7:0] in_array[2],
    output logic [7:0] out_array[2]
);
    import "DPI-C" function void process_array_imp(input byte arr[]);
    export "DPI-C" task process_array_exp;
    task automatic process_array_exp;
        input logic [7:0] arr_in_exp[];
        output logic [7:0] arr_out_exp[];
    begin
        if (arr_in_exp.size() == arr_out_exp.size()) begin
            for (int i = 0; i < arr_in_exp.size(); i++) begin
                arr_out_exp[i] = arr_in_exp[i] + 8'd1;
            end
        end
    end
    endtask
    always_comb begin
        byte temp_in_byte [2];
        logic [7:0] temp_in_bit [2];
        logic [7:0] temp_out_bit [2];
        int i;
        for (i=0; i<2; i++) begin
            temp_in_byte[i] = byte'(in_array[i]);
        end
        process_array_imp(temp_in_byte);
        for (i=0; i<2; i++) begin
            temp_in_bit[i] = in_array[i] + 8'd2;
        end
        process_array_exp(temp_in_bit, temp_out_bit);
         for (i=0; i<2; i++) begin
            out_array[i] = temp_out_bit[i];
        end
    end
endmodule
module module_string_chandle (
    input logic [7:0] str_in_val,
    output logic [7:0] ch_out_val
);
    import "DPI-C" function string get_string_from_int(int val);
    import "DPI-C" function chandle create_handle(string s);
    import "DPI-C" function int read_handle(chandle h);
    string current_string;
    chandle current_handle;
    int handle_value;
    always_comb begin
        current_string = get_string_from_int(str_in_val);
        current_handle = create_handle(current_string);
        handle_value = read_handle(current_handle);
        ch_out_val = handle_value;
    end
endmodule

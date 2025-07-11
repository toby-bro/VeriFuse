module SformatfModule(
    input int in_int,
    input real in_real,
    input string in_string,
    input bit enable_op,
    output string out_string_sformatf,
    output string out_string_psprintf
);
always_comb begin
    if (enable_op) begin
        out_string_sformatf = $sformatf("Int: %0d, Real: %f, String: %s", in_int, in_real, in_string);
        out_string_psprintf = $psprintf("Integer (hex): %0h, Real Value: %f", in_int, in_real);
    end else begin
        out_string_sformatf = "";
        out_string_psprintf = "";
    end
end
endmodule
module ValuePlusArgsModule(
    input bit enable_args_check,
    output int plusarg_int_val,
    output real plusarg_real_val,
    output bit plusarg_success_int,
    output bit plusarg_success_real
);
int temp_int;
real temp_real;
always_comb begin
    if (enable_args_check) begin
        plusarg_success_int = $value$plusargs("my_int_arg=%d", temp_int);
        plusarg_success_real = $value$plusargs("my_real_arg=%f", temp_real);
    end else begin
        temp_int = 0;
        temp_real = 0.0;
        plusarg_success_int = 0;
        plusarg_success_real = 0;
    end
    plusarg_int_val = temp_int;
    plusarg_real_val = temp_real;
end
endmodule
class MyRandomizableClass;
    rand int class_rand_int;
    rand logic [3:0] class_rand_array [2];
    constraint class_int_range { class_rand_int inside {[1:100]}; }
    constraint array_elem_range { class_rand_array[0] < 10; class_rand_array[1] < 10; }
endclass
module ClassRandomizeModule(
    input bit clk,
    input bit trigger_rand_class,
    output int out_class_rand_int,
    output logic [3:0] out_class_rand_array [2],
    output bit class_rand_result
);
MyRandomizableClass my_obj = null;
always_ff @(posedge clk) begin
    if (my_obj == null) begin
        my_obj = new();
    end
    if (trigger_rand_class && my_obj != null) begin
        if (my_obj.randomize(class_rand_int, class_rand_array) with { class_rand_int > 50; }) begin
            class_rand_result = 1;
        end else begin
            class_rand_result = 0;
        end
    end else begin
        class_rand_result = 0;
    end
    if (my_obj != null) begin
        out_class_rand_int = my_obj.class_rand_int;
        out_class_rand_array = my_obj.class_rand_array;
    end else begin
        out_class_rand_int = 'x;
        out_class_rand_array = '{'x,'x};
    end
end
endmodule
class ScopeRandomizable;
    rand int scope_int_non_rand;
    rand logic [7:0] scope_byte_non_rand;
    constraint scope_int_constr { scope_int_non_rand > 10; };
    constraint scope_byte_constr { scope_byte_non_rand != 0; };
endclass
module ScopeRandomizeModule(
    input bit clk,
    input bit trigger_rand_scope,
    output int out_scope_rand_int,
    output logic [7:0] out_scope_rand_byte,
    output bit scope_rand_result
);
    ScopeRandomizable scope_obj = null;
    always_ff @(posedge clk) begin
        if (scope_obj == null) begin
            scope_obj = new();
        end
        if (trigger_rand_scope && scope_obj != null) begin
            scope_rand_result <= scope_obj.randomize();
        end else begin
            scope_rand_result <= 0;
        end
        if (scope_obj != null) begin
            out_scope_rand_int <= scope_obj.scope_int_non_rand;
            out_scope_rand_byte <= scope_obj.scope_byte_non_rand;
        end else begin
            out_scope_rand_int <= 'x;
            out_scope_rand_byte <= 'x;
        end
    end
endmodule
module GlobalClockModule(
    input bit clk_in,
    input bit enable_prop,
    output bit assertion_eval_out
);
    // Remove global clocking block and rewrite property as a simple assertion
    property check_global_clock_prop;
        @(posedge clk_in) disable iff (!enable_prop) 1;
    endproperty
    assert property (check_global_clock_prop);
    always_comb begin
        assertion_eval_out = enable_prop;
    end
endmodule
module InferredValueModule(
    input bit clk_in,
    input bit disable_sig_in,
    input bit check_sig_in,
    output bit prop_inferred_success_out,
    output bit prop_explicit_success_out
);
    // Remove default clocking block and use explicit property clocks
    property check_inferred_defaults_prop;
        @(posedge clk_in) disable iff (disable_sig_in) check_sig_in |-> 1;
    endproperty
    property check_explicit_prop;
        @(posedge clk_in) disable iff (disable_sig_in) check_sig_in |-> 1;
    endproperty
    assert property (check_inferred_defaults_prop);
    assert property (check_explicit_prop);
    always_comb begin
        prop_inferred_success_out = check_sig_in && disable_sig_in;
        prop_explicit_success_out = check_sig_in || disable_sig_in;
    end
endmodule
module SequenceMethodModule(
    input bit clk,
    input bit data_in1,
    input bit data_in2,
    input bit enable_seq_prop,
    output bit seq_property_eval
);
    sequence my_sequence (a, b);
        @(posedge clk) a ##1 b;
    endsequence
    property check_sequence_methods_prop;
        ( my_sequence(data_in1, data_in2).triggered || my_sequence(data_in1, data_in2).matched ) |-> 1;
    endproperty
    assert property (@(posedge clk) enable_seq_prop |-> check_sequence_methods_prop);
    always_comb begin
        seq_property_eval = data_in1 || data_in2 || enable_seq_prop;
    end
endmodule

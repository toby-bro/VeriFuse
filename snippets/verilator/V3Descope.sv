module mod_simple_ref (
    input logic i_data,
    output logic o_result
);
    logic internal_sig;
    always_comb begin
        internal_sig = i_data;
        o_result = internal_sig;
    end
endmodule
module mod_func_call (
    input logic [7:0] i_val,
    output logic [7:0] o_squared
);
    function automatic logic [7:0] square_func (input logic [7:0] val_in);
        return val_in * val_in;
    endfunction : square_func
    always_comb begin
        o_squared = square_func(i_val);
    end
endmodule
module mod_generate_if (
    input logic i_select,
    input logic i_a,
    input logic i_b,
    output logic o_mux_out
);
    logic internal_common;
    generate
        if (1) begin : gen_true
            logic internal_true;
            always_comb begin
                internal_true = i_a;
                o_mux_out = internal_true;
                internal_common = 1'b1;
            end
        end else begin : gen_false
            logic internal_false;
        end
    endgenerate
    always_comb begin
        internal_common = internal_common ^ i_select;
    end
endmodule
module mod_named_block (
    input logic i_start,
    output logic o_done
);
    logic top_level_sig;
    my_scope_a: begin
        logic block_sig_a;
        always_comb begin
            top_level_sig = i_start;
            block_sig_a = top_level_sig;
        end
    end : my_scope_a
    my_scope_b: begin
        logic block_sig_b;
        always_comb begin
            block_sig_b = my_scope_a.block_sig_a;
            o_done = block_sig_b;
        end
    end : my_scope_b
endmodule
module mod_hier_func_call (
    input logic i_value,
    output logic o_processed_value
);
    my_func_scope: begin
        function automatic logic process_it (input logic val_in);
            return ~val_in;
        endfunction : process_it
    end : my_func_scope
    always_comb begin
        o_processed_value = my_func_scope.process_it(i_value);
    end
endmodule
module mod_class_inst (
    input logic i_enable,
    input logic i_data_in,
    output logic o_data_out
);
    class MyClass;
        logic my_member;
        function new();
            my_member = 1'b0;
        endfunction
        function void set_member(logic val);
            my_member = val;
        endfunction : set_member
        function logic get_member();
            return my_member;
        endfunction : get_member
    endclass
    MyClass my_object_handle;
    function automatic logic process_with_class(input logic enable_in, input logic data_in);
        logic result;
        if (enable_in) begin
            my_object_handle = new();
            my_object_handle.set_member(data_in);
            result = my_object_handle.get_member();
        end else begin
            my_object_handle = null;
            result = 1'b0;
        end
        return result;
    endfunction : process_with_class
    always_comb begin
        o_data_out = process_with_class(i_enable, i_data_in);
    end
endmodule

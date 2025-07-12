typedef class forward_my_class_t;
typedef struct { int data; } my_struct_t;
class forward_my_class_t;
    int data;
    function new(); data = 0; endfunction
endclass

class class_with_typedefs;
    local typedef int local_int_t;
    protected typedef real protected_real_t;
    typedef my_struct_t my_internal_struct_t;
    local_int_t local_var;
    protected_real_t protected_var;
    my_internal_struct_t struct_var_in_class;
    function new();
        local_var = 1;
        protected_var = 1.0;
        struct_var_in_class.data = 1;
    endfunction
endclass

module m_class_and_typedefs (
    input logic trigger_in,
    output int class_var_data_out,
    output int forward_class_data_out,
    output int local_var_out,
    output real protected_var_out
);
    class_with_typedefs my_class_h = null;
    forward_my_class_t my_forward_class_h = null;
    always_comb begin
        if (trigger_in) begin
            my_class_h = new();
            my_forward_class_h = new();
            class_var_data_out = my_class_h.struct_var_in_class.data;
            local_var_out = my_class_h.local_var;
            protected_var_out = my_class_h.protected_var;
            my_forward_class_h.data = 10;
            forward_class_data_out = my_forward_class_h.data;
        end else begin
            my_class_h = null;
            my_forward_class_h = null;
            class_var_data_out = 0;
            local_var_out = 0;
            protected_var_out = 0.0;
            forward_class_data_out = 0;
        end
    end
endmodule


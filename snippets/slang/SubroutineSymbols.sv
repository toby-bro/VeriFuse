module basic_subroutines (
    input logic enable,
    input int data_in,
    output logic simple_task_done,
    output int simple_func_result
);
    function automatic int simple_func(input int a, input int b);
        return a + b;
    endfunction
    task automatic simple_task(input int data, output logic done);
        done = (data > 0);
    endtask
    always_comb begin
        simple_func_result = 0;
        simple_task_done = 1'b0;
        if (enable) begin
            simple_func_result = simple_func(data_in, 10);
            simple_task(data_in, simple_task_done);
        end else begin
            simple_func_result = simple_func(data_in, 5);
            simple_task(0, simple_task_done);
        end
    end
endmodule
module ref_args (
    input int value_in,
    input int add_val,
    output int value_out,
    output int const_ref_val_out
);
    function automatic int modify_ref_func(ref int x, input int increment);
        x = x + increment;
        return x;
    endfunction
    task automatic read_const_ref(const ref int y, output int out);
        out = y * 2;
    endtask
    int temp_val;
    int const_ref_temp;
    always_comb begin
        temp_val = value_in;
        value_out = modify_ref_func(temp_val, add_val);
        const_ref_temp = value_in + 1;
        read_const_ref(const_ref_temp, const_ref_val_out);
    end
endmodule
class my_class;
    int member_var;
    local int local_var;
    function new(input int initial_val);
        this.member_var = initial_val;
        this.local_var = 99;
    endfunction
    function int get_value();
        return this.member_var;
    endfunction
    protected virtual function void protected_method(input int val);
        this.member_var = val;
    endfunction
    static function int add_values(input int a, input int b);
        return a + b;
    endfunction
    task automatic set_value(input int new_val);
        this.member_var = new_val;
    endtask
    local function int local_getter();
        return this.member_var + this.local_var;
    endfunction
    function int call_protected_and_local(input int val);
        protected_method(val);
        return local_getter();
    endfunction
endclass
module class_methods (
    input int data_in,
    input int static_add1,
    input int static_add2,
    output int data_out,
    output int static_result,
    output int local_check_out
);
    my_class inst1;
    always_comb begin
        if (inst1 == null) begin
            inst1 = new(data_in);
        end
        data_out = inst1.get_value();
        static_result = my_class::add_values(static_add1, static_add2);
        inst1.set_value(data_in + 10);
        local_check_out = inst1.call_protected_and_local(data_in * 2);
    end
endmodule
class base_c;
    int base_data;
    function new();
        base_data = 0;
    endfunction
    virtual function int get_data();
        return base_data;
    endfunction
    virtual function void display_data();
    endfunction
    virtual function int get_final_data();
        return base_data + 100;
    endfunction
endclass // base_c
class derived_c extends base_c;
    int derived_data;
    function new();
        super.new();
        derived_data = 0;
    endfunction
    virtual function int get_data();
        return super.get_data() + derived_data;
    endfunction
    virtual function void display_data();
    endfunction
endclass
module class_override_features (
    input int base_val_in,
    input int derived_val_in,
    output int overridden_data_out,
    output int base_final_data_out
);
    derived_c inst_derived;
    base_c inst_base;
    always_comb begin
        if (inst_derived == null) begin
            inst_derived = new();
        end
        inst_base = inst_derived;
        inst_derived.base_data = base_val_in;
        inst_derived.derived_data = derived_val_in;
        overridden_data_out = inst_derived.get_data();
        base_final_data_out = inst_base.get_final_data();
    end
endmodule
class complex_class;
    int internal_data;
    function new();
        internal_data = 0;
    endfunction
    extern function int process_data(input int x);
    extern task automatic update_data(input int y);
    function int get_internal_data();
        return this.internal_data;
    endfunction
endclass
function int complex_class::process_data(input int x);
    this.internal_data = x + 5;
    return this.internal_data * 2;
endfunction
task automatic complex_class::update_data(input int y);
    this.internal_data = y - 10;
endtask
module out_of_block (
    input int in_val,
    input int update_val,
    output int out_val,
    output int updated_internal_data
);
    complex_class inst_complex;
    always_comb begin
        if (inst_complex == null) begin
            inst_complex = new();
        end
        out_val = inst_complex.process_data(in_val);
        inst_complex.update_data(update_val);
        updated_internal_data = inst_complex.get_internal_data();
    end
endmodule
class default_arg_class;
    int member_offset;
    function new(input int offset = 0);
        member_offset = offset;
    endfunction
    function int add_with_default(input int x, input int y = 7);
        return x + y + member_offset;
    endfunction
endclass
class derived_default_arg_class extends default_arg_class;
    int extra_offset;
    function new(input int initial_offset = 0, input int extra = 5);
        super.new(initial_offset);
        extra_offset = extra;
    endfunction
    function int get_total_offset();
        return member_offset + extra_offset;
    endfunction
endclass
module default_args (
    input int val1,
    input int val2,
    input int offset_in,
    input int derived_extra_in,
    output int result_with_default,
    output int result_no_default,
    output int ctor_default_result,
    output int ctor_no_default_result,
    output int derived_ctor_default_inherit,
    output int derived_ctor_no_default_inherit
);
    default_arg_class inst_default;
    default_arg_class inst_no_default;
    default_arg_class inst_ctor_default;
    default_arg_class inst_ctor_no_default;
    derived_default_arg_class inst_derived_default;
    derived_default_arg_class inst_derived_no_default;
    always_comb begin
        if (inst_ctor_default == null) begin
            inst_ctor_default = new();
        end
        if (inst_ctor_no_default == null) begin
            inst_ctor_no_default = new(offset_in);
        end
            if (inst_default == null) begin
                inst_default = new(1);
        end
            if (inst_no_default == null) begin
                inst_no_default = new(2);
        end
        if (inst_derived_default == null) begin
            inst_derived_default = new(offset_in + 10, derived_extra_in);
        end
            if (inst_derived_no_default == null) begin
                inst_derived_no_default = new();
        end
        result_with_default = inst_default.add_with_default(val1);
        result_no_default = inst_no_default.add_with_default(val1, val2);
        ctor_default_result = inst_ctor_default.member_offset;
        ctor_no_default_result = inst_ctor_no_default.member_offset;
        derived_ctor_default_inherit = inst_derived_default.get_total_offset();
        derived_ctor_no_default_inherit = inst_derived_no_default.get_total_offset();
    end
endmodule
module dpi_example (
    input int data_in_dpi,
    input int factor_dpi,
    output int func_result_dpi,
    output logic task_done_dpi
);
    import "DPI-C" function int c_add(input int a, input int b);
    import "DPI-C" pure function int c_pure_multiply(input int a, input int b);
    import "DPI-C" context task automatic c_process_data(input int val, output logic done);
    int temp_c_add_result;
    int temp_c_pure_multiply_result;
    logic temp_task_done; 
    always_comb begin
        temp_c_add_result = c_add(data_in_dpi, 10);
        temp_c_pure_multiply_result = c_pure_multiply(data_in_dpi, factor_dpi);
        func_result_dpi = temp_c_add_result + temp_c_pure_multiply_result;
        c_process_data(data_in_dpi, temp_task_done);
        task_done_dpi = temp_task_done; 
    end
endmodule
interface class my_interface;
    pure virtual function int process(input int val);
endclass
class my_implementor implements my_interface;
    int processed_count;
    function new();
        processed_count = 0;
    endfunction
    virtual function int process(input int val);
        processed_count = processed_count + 1;
        return val * 3 + processed_count;
    endfunction
    function int get_processed_count();
        return processed_count;
    endfunction
endclass
module interface_class_extern (
    input int iface_in,
    output int iface_out,
    output int processed_count_out
);
    my_implementor impl;
    always_comb begin
        if (impl == null) begin
            impl = new();
        end
        iface_out = impl.process(iface_in);
        processed_count_out = impl.get_processed_count();
    end
endmodule
interface extern_if;
    extern function int extern_func(input int a);
    extern task automatic extern_task(input int b, output logic done);
endinterface
module module_extern_if_impl (
    input int extern_func_in,
    input int extern_task_in,
    output int extern_func_out,
    output logic extern_task_done_out
);
    extern_if vif();
    function int vif.extern_func(input int a);
        return a + 5;
    endfunction
    task automatic vif.extern_task(input int b, output logic done);
        done = (b > 10);
    endtask
    logic temp_task_done; 
    always_comb begin
        extern_func_out = vif.extern_func(extern_func_in);
        vif.extern_task(extern_task_in, temp_task_done);
        extern_task_done_out = temp_task_done; 
    end
endmodule
virtual class abstract_base;
    pure virtual function int calculate(input int val);
endclass
class concrete_derived extends abstract_base;
    function new(); endfunction
    function int calculate(input int val);
        return val * 5;
    endfunction
endclass
module pure_virtual_example (
    input int calc_in,
    output int calc_out
);
    concrete_derived inst;
    always_comb begin
        if (inst == null) begin
            inst = new();
        end
        calc_out = inst.calculate(calc_in);
    end
endmodule
module ref_arg_automatic_context (
    input int data_in,
    output int data_out_ref
);
    int internal_data = 0;
    task automatic update_data_ref(ref int data, input int add);
        data = data + add;
    endtask
    always_comb begin
        update_data_ref(internal_data, data_in);
        data_out_ref = internal_data;
    end
endmodule
interface class iface_with_default_proto;
    pure virtual function int process_with_default(input int a = 10);
endclass // Corrected from endinterface to endclass

class class_with_default_impl implements iface_with_default_proto;
    int result_offset = 5;
    virtual function int process_with_default(input int a = 10);
        return a + result_offset;
    endfunction
endclass

module default_proto_user (
    input int in_val,
    output int out_val
);
    class_with_default_impl inst;
    always_comb begin
        if (inst == null) inst = new();
        out_val = inst.process_with_default(in_val);
    end
endmodule
interface modport_iface;
    function int calculate(input int x, input int y);
        return x - y;
    endfunction
    modport mp_imp (
        import calculate
    );
    modport mp_exp (
        export calculate
    );
endinterface
module modport_user (
    input int val1,
    input int val2,
    output int result_imp,
    output int result_exp
);
    modport_iface vif();
    always_comb begin
        result_imp = vif.mp_imp.calculate(val1, val2);
        result_exp = vif.mp_exp.calculate(val1, val2);
    end
endmodule
class class_with_proto;
    int data;
    function new(int initial_data); data = initial_data; endfunction
    function int process_internal(input int val);
        return data * val;
    endfunction
endclass
module proto_class_user (
    input int in_data,
    input int factor,
    output int out_result
);
    class_with_proto inst;
    always_comb begin
        if (inst == null) inst = new(in_data);
        out_result = inst.process_internal(factor);
    end
endmodule
class visibility_base;
    int value = 10;
    virtual protected function int get_protected_value(input int offset);
        return value + 1 + offset;
    endfunction
endclass
class visibility_derived extends visibility_base;
    int value = 20;
    virtual protected function int get_protected_value(input int offset);
        return value + 2 + offset;
    endfunction
    function int get_protected_value_public(input int offset);
        return get_protected_value(offset);
    endfunction
endclass
module visibility_user (
    input int derived_val,
    input int offset_in,
    output int derived_override_pub
);
    visibility_derived inst;
    always_comb begin
        if (inst == null) begin
            inst = new();
        end
        inst.value = derived_val;
        derived_override_pub = inst.get_protected_value_public(offset_in);
    end
endmodule
class base_with_local_default_ctor;
    local int local_const = 100;
    int data;
    function new(input int initial_data = 100); 
        data = initial_data;
    endfunction
    function int get_data(); return data; endfunction
endclass
class derived_inheriting_local_default extends base_with_local_default_ctor;
    function new();
        super.new(); 
    endfunction
endclass
module local_default_ctor_user (
    input logic dummy_in,
    output int derived_data_out
);
    derived_inheriting_local_default inst;
    always_comb begin
        if (inst == null) begin
            inst = new();
        end
        derived_data_out = inst.get_data();
    end
endmodule
class base_with_ctor_defaults;
    int data;
    function new(input int a = 10, input int b = 20);
        data = a + b;
    endfunction
    function int get_data(); return data; endfunction
endclass
class derived_inheriting_ctor_defaults extends base_with_ctor_defaults;
    int extra;
    function new(input int a = 10, input int b = 20, input int c = 30);
        super.new(a, b);
        extra = c;
    endfunction
    function int get_total(); return get_data() + extra; endfunction
endclass
module defaulted_super_arg_user (
    input logic dummy_in,
    output int total_default_out,
    output int total_override_out
);
    derived_inheriting_ctor_defaults inst_default;
    derived_inheriting_ctor_defaults inst_override;
    always_comb begin
        if (inst_default == null) begin
            inst_default = new(); 
        end
        if (inst_override == null) begin
            inst_override = new(50, 60, 40); 
        end
        total_default_out = inst_default.get_total();
        total_override_out = inst_override.get_total();
    end
endmodule
class base_for_extends;
    int value = 1;
    virtual function void process(ref int data);
        data = data + value;
    endfunction
endclass
class derived_using_extends extends base_for_extends;
    int extra = 10;
    function void process(ref int data);
        super.process(data);
        data = data + extra;
    endfunction
endclass
module extends_user (
    input int data_in,
    output int data_out
);
    derived_using_extends inst;
    int temp_data;
    always_comb begin
        if (inst == null) begin
            inst = new();
        end
        temp_data = data_in;
        inst.process(temp_data);
        data_out = temp_data;
    end
endmodule
class class_with_initial;
    int value = 0;
    function void set_initial_value();
        value = 50;
    endfunction
    function int get_value(); return value; endfunction
endclass
module initial_user (
    input logic dummy_in,
    output int initial_value_out
);
    class_with_initial inst;
    always_comb begin
        if (inst == null) begin
            inst = new();
            inst.set_initial_value();
        end
        initial_value_out = inst.get_value();
    end
endmodule
interface extern_if_forkjoin;
    extern task automatic forkjoin_task(input int val);
endinterface
module module_extern_if_forkjoin_impl (
    input int task_in,
    output logic dummy_out
);
    extern_if_forkjoin vif();
    task automatic vif.forkjoin_task(input int val);
        dummy_out = (val > 5);
    endtask
    logic temp_dummy_out;
    always_comb begin
        vif.forkjoin_task(task_in);
    end
endmodule

class my_base_class;
    int base_val;
    function new(int val = 10);
        base_val = val;
    endfunction
endclass

class my_base_class_def;
    int val;
    function new(int v = 100);
        val = v;
    endfunction
endclass

class my_derived_class extends my_base_class;
    int derived_val;
    function new(int derived_init = 20);
        super.new();
        derived_val = derived_init;
    endfunction
endclass

class my_derived_class_def extends my_base_class_def;
    function new(int dummy_arg = 0);
        super.new();
    endfunction
endclass

class my_derived_class_super_explicit extends my_base_class;
    int extra_val;
    function new(int arg1, int arg2);
        super.new(arg1);
        extra_val = arg2;
    endfunction
endclass

module new_classes (
    input int in_base_val,
    input int in_derived_super_arg1,
    input int in_derived_super_arg2,
    input int in_derived_val,
    output int out_base_val,
    output int out_derived_super_default_base,
    output int out_derived_super_explicit_base,
    output int out_derived_super_explicit_extra,
    output int out_derived_val
);
    my_base_class base_h;
    my_derived_class derived_h;
    my_derived_class derived_h_with_args;
    my_derived_class_def derived_h_def;
    my_derived_class_super_explicit derived_h_super_explicit;
    always_comb begin
        base_h = new(in_base_val);
        derived_h = new();
        derived_h_with_args = new(in_derived_val);
        derived_h_def = new();
        derived_h_super_explicit = new(in_derived_super_arg1, in_derived_super_arg2);
        if (base_h != null) out_base_val = base_h.base_val; else out_base_val = -1;
        if (derived_h != null) begin
            out_derived_val = derived_h.derived_val;
            out_derived_super_default_base = derived_h.base_val;
        end else begin
            out_derived_val = -1;
            out_derived_super_default_base = -1;
        end
        if (derived_h_super_explicit != null) begin
            out_derived_super_explicit_base = derived_h_super_explicit.base_val;
            out_derived_super_explicit_extra = derived_h_super_explicit.extra_val;
        end else begin
            out_derived_super_explicit_base = -1;
            out_derived_super_explicit_extra = -1;
        end
    end
endmodule


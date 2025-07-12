class base_class;
    int base_val;
    function new(int v);
        base_val = v;
    endfunction
    function int get_base_val();
        return base_val;
    endfunction
endclass

class derived_class extends base_class;
    int derived_val;
    function new(int v1, int v2);
        super.new(v1);
        derived_val = v2;
    endfunction
    function int get_derived_val();
        return derived_val;
    endfunction
endclass

module mod_class_inheritance (
    input int input_val,
    output int output_val
);
    derived_class derived_inst;
    initial begin
        derived_inst = new(input_val, input_val * 2);
    end
    always_comb begin
        output_val = derived_inst.get_base_val() + derived_inst.get_derived_val();
    end
endmodule


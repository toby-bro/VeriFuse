module class_extends_mod (
    input int derived_val_i,
    output int result_o,
    input int base_val_i
);
    class BaseClass;
        int base_member;
        function new(int val);
            base_member = val;
        endfunction
        function int get_base();
            return base_member;
        endfunction
    endclass
    class DerivedClass extends BaseClass;
        int derived_member;
        function new(int b_val, int d_val);
            super.new(b_val);
            derived_member = d_val;
        endfunction
        function int get_derived();
            return derived_member;
        endfunction
        function int sum_members();
            return base_member + derived_member;
        endfunction
    endclass
    DerivedClass derived_instance;
    int calculation_result;
    always_comb begin
        derived_instance = new(base_val_i, derived_val_i);
        calculation_result = derived_instance.sum_members();
    end
    assign result_o = calculation_result;
endmodule


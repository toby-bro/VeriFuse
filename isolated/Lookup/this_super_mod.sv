class BaseClassThisSuper;
    int base_prop = 300;
    function new(int val);
        base_prop = val;
    endfunction
    function automatic int get_base_prop();
        return base_prop;
    endfunction
endclass

class DerivedClassThisSuper extends BaseClassThisSuper;
    int derived_prop = 400;
    function new(int val1, int val2);
        super.new(val1);
        this.derived_prop = val2;
    endfunction
    function automatic int get_derived_sum();
        return this.get_base_prop() + super.get_base_prop() + this.derived_prop;
    endfunction
endclass

module this_super_mod (
    input int in_val1,
    input int in_val2,
    output int out_val
);
    DerivedClassThisSuper instance_h;
    int local_tsm;
    always_comb begin
        if (instance_h == null) instance_h = new(in_val1, in_val2);
        local_tsm = instance_h.get_derived_sum();
    end
    assign out_val = local_tsm;
endmodule


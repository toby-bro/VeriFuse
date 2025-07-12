class ClassLookupParent;
    int parent_prop = 500;
endclass

class ClassLookupChild extends ClassLookupParent;
    function automatic int get_parent_prop_via_this();
        return this.parent_prop;
    endfunction
    function automatic int get_parent_prop_via_super();
        return super.parent_prop;
    endfunction
endclass

module class_lookup_internal_mod (
    input int dummy_in,
    output int out_val
);
    ClassLookupChild instance_h;
    int local_clim;
    always_comb begin
        if (instance_h == null) instance_h = new();
        local_clim = instance_h.get_parent_prop_via_this() +
            instance_h.get_parent_prop_via_super();
    end
    assign out_val = local_clim;
endmodule


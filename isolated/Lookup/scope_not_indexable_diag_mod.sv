class MyClassInstance;
    int instance_prop;
    function new(int initial_val);
        instance_prop = initial_val;
    endfunction
    function int get_instance_prop();
        return instance_prop;
    endfunction
endclass

module scope_not_indexable_diag_mod (
    input int in_val,
    output int out_val
);
    MyClassInstance instance_h;
    int local_snidm;
    always_comb begin
        if (instance_h == null) instance_h = new(in_val);
        local_snidm = instance_h.instance_prop;
    end
    assign out_val = local_snidm;
endmodule


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
endclass

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
    output int base_final_data_out,
    output int overridden_data_out
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


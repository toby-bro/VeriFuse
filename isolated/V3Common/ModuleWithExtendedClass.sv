class BaseClass;
    logic base_member;
    function new(logic b);
        base_member = b;
    endfunction
endclass

class DerivedClass extends BaseClass;
    logic derived_member;
    function new(logic b, logic d);
        super.new(b);
        derived_member = d;
    endfunction
endclass

module ModuleWithExtendedClass (
    input logic base_in,
    output logic derived_out
);
    DerivedClass derived_instance;
    always_comb begin
        derived_instance = new(base_in, 1'b1);
        derived_out = derived_instance.base_member && derived_instance.derived_member;
    end
endmodule


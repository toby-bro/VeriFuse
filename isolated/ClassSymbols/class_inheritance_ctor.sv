typedef class BaseRequiresArgs;
typedef class DerivedExtendsArgsNoSuper;
class Base;
    int base_data;
    function new(int d);
        base_data = d;
    endfunction
endclass

class BaseForAutoCtorValid;
    int data_b = 111;
    function new(int bd_val = 101);
        data_b = bd_val;
    endfunction
endclass

class BaseForInvalidExtendsDefault;
    int data = 1;
    function new(int required_arg);
        data = required_arg;
    endfunction
endclass

class BaseRequiresArgs;
    int base_val;
    function new(int arg);
        base_val = arg;
    endfunction
endclass

class Derived extends Base;
    int derived_data;
    function new(int bd, int dd);
        super.new(bd);
        derived_data = dd;
    endfunction
endclass

class DerivedAutoCtorValid extends BaseForAutoCtorValid;
    int extra_d = 202;
endclass

class DerivedExtendsArgsAndSuper extends Base;
    int data_d = 1;
    function new(int bd, int dd);
        super.new(bd);
        data_d = dd;
    endfunction
endclass

class DerivedExtendsArgsNoSuper extends BaseRequiresArgs;
    int derived_data = 3;
    function new(int d);
        super.new(d);
        derived_data = d;
    endfunction
endclass

class DerivedInvalidExtendsDefault extends BaseForInvalidExtendsDefault;
    int data_d = 2;
    function new(int required_arg, int dd);
        super.new(required_arg);
        data_d = dd;
    endfunction
endclass

module class_inheritance_ctor (
    input int base_d_in,
    input int derived_d_in,
    input logic en,
    input int extends_args_no_super_d_in,
    input int invalid_default_dd_in,
    input int invalid_default_req_arg_in,
    output logic [31:0] auto_ctor_out,
    output logic [31:0] derived_out,
    output logic extends_args_no_super_inst_en,
    output logic [31:0] extends_args_no_super_out,
    output logic extends_args_super_inst_en,
    output logic [31:0] extends_args_super_out,
    output logic invalid_extends_default_inst_en,
    output logic [31:0] invalid_extends_default_out
);
    Derived                     derived_inst;
    DerivedAutoCtorValid        derived_auto_valid_inst;
    DerivedExtendsArgsNoSuper   extends_args_no_super_inst;
    DerivedExtendsArgsAndSuper  extends_args_super_inst;
    DerivedInvalidExtendsDefault invalid_extends_default_inst;
    always_comb begin
        if (en) begin
            derived_inst = new(base_d_in, derived_d_in);
            derived_out  = derived_inst.base_data + derived_inst.derived_data;
            derived_auto_valid_inst = new();
            auto_ctor_out = derived_auto_valid_inst.data_b + derived_auto_valid_inst.extra_d;
            extends_args_no_super_inst = new(extends_args_no_super_d_in);
            extends_args_no_super_out  = extends_args_no_super_inst.derived_data;
            extends_args_no_super_inst_en = 1;
            extends_args_super_inst = new(base_d_in, derived_d_in);
            extends_args_super_out  = extends_args_super_inst.base_data + extends_args_super_inst.data_d;
            extends_args_super_inst_en = 1;
            invalid_extends_default_inst = new(invalid_default_req_arg_in, invalid_default_dd_in);
            invalid_extends_default_out = invalid_extends_default_inst.data_d;
            invalid_extends_default_inst_en = 1;
        end else begin
            derived_inst = null;
            derived_out  = 0;
            derived_auto_valid_inst = null;
            auto_ctor_out = 0;
            extends_args_no_super_inst = null;
            extends_args_no_super_out  = 0;
            extends_args_no_super_inst_en = 0;
            extends_args_super_inst = null;
            extends_args_super_out  = 0;
            extends_args_super_inst_en = 0;
            invalid_extends_default_inst = null;
            invalid_extends_default_out = 0;
            invalid_extends_default_inst_en = 0;
        end
    end
endmodule


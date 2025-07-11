typedef class CyclicA;
typedef class CyclicB;
typedef class ForwardDeclaredClass;
typedef class BaseRequiresArgs;
typedef class DerivedExtendsArgsNoSuper;
typedef class ImplementsNonIfaceError;
interface class MyInterface;
    pure virtual function int get_value();
    pure virtual task do_action();
endclass
interface class MyInterface2;
    pure virtual function int get_value_offset(int offset);
endclass
interface class DerivedInterface extends MyInterface;
    pure virtual function void another_method();
endclass
interface class BadBaseIface;
    pure virtual function int dummy();
endclass
interface class InterfaceDiamond1;
    pure virtual function int common_method();
endclass
interface class InterfaceDiamond2;
    pure virtual function int common_method();
endclass
class CyclicB;
    int b_prop;
    CyclicA a_inst;
    function new(int val_b);
        b_prop = val_b;
    endfunction
endclass
class CyclicA;
    int a_prop;
    CyclicB b_inst;
    function new(int val_a);
        a_prop = val_a;
    endfunction
endclass
class ForwardDeclaredClass;
    int value;
    function new(int v);
        value = v;
    endfunction
endclass
class Basic;
    int data;
    function new();
        data = 5;
    endfunction
    function int getData();
        return data;
    endfunction
endclass
class Base;
    int base_data;
    function new(int d);
        base_data = d;
    endfunction
endclass
class Derived extends Base;
    int derived_data;
    function new(int bd, int dd);
        super.new(bd);
        derived_data = dd;
    endfunction
endclass
class BaseForAutoCtorValid;
    int data_b = 111;
    function new(int bd_val = 101);
        data_b = bd_val;
    endfunction
endclass
class DerivedAutoCtorValid extends BaseForAutoCtorValid;
    int extra_d = 202;
endclass
class BaseConstructorNoArgs;
    int data = 1;
    function new();
        data = 2;
    endfunction
endclass
class BaseRequiresArgs;
    int base_val;
    function new(int arg);
        base_val = arg;
    endfunction
endclass
class DerivedExtendsArgsNoSuper extends BaseRequiresArgs;
    int derived_data = 3;
    function new(int d);
        super.new(d);
        derived_data = d;
    endfunction
endclass
class DerivedExtendsArgsAndSuper extends Base;
    int data_d = 1;
    function new(int bd, int dd);
        super.new(bd);
        data_d = dd;
    endfunction
endclass
class BaseForInvalidExtendsDefault;
    int data = 1;
    function new(int required_arg);
        data = required_arg;
    endfunction
endclass
class DerivedInvalidExtendsDefault extends BaseForInvalidExtendsDefault;
    int data_d = 2;
    function new(int required_arg, int dd);
        super.new(required_arg);
        data_d = dd;
    endfunction
endclass
class CannotExtend extends Basic;
    int data = 5;
    function int get_data();
        return data;
    endfunction
    function new();
        data = 5;
    endfunction
endclass
class ExtendsFinal extends CannotExtend;
    int val = 1;
    function int get_val();
        return val;
    endfunction
    function new();
        val = 1;
    endfunction
endclass
class ExtendsInterface implements MyInterface;
    int val = 1;
    function new();
        val = 1;
    endfunction
    virtual function int get_value();
        return val;
    endfunction
    virtual task do_action();
        val++;
    endtask
endclass
class ImplementsNonClass implements MyInterface;
    int val = 1;
    function new();
        val = 2;
    endfunction
    virtual function int get_value();
        return val;
    endfunction
    virtual task do_action();
        val++;
    endtask
endclass
class ImplementsNonIfaceError extends Basic;
    int val = 1;
    function new();
        val = 2;
    endfunction
endclass
class InterfaceDiamondImpl implements InterfaceDiamond1, InterfaceDiamond2;
    virtual function int common_method();
        return 1;
    endfunction
    function new();
    endfunction
endclass
virtual class AbstractBase;
    int base_prop = 99;
    pure virtual function int get_val();
    pure virtual task do_abstract_action();
    function new();
        base_prop = 99;
    endfunction
endclass
class ConcreteDerived extends AbstractBase;
    int derived_prop = 1;
    function new();
        base_prop = 100;
        derived_prop = 2;
    endfunction
    virtual function int get_val();
        return derived_prop + base_prop;
    endfunction
    virtual task do_abstract_action();
        derived_prop++;
    endtask
endclass
class DerivedNonAbstractIncomplete extends AbstractBase;
    int my_prop = 10;
    function new();
        my_prop = 11;
    endfunction
    function int get_my_prop();
        return my_prop;
    endfunction
    virtual function int get_val();
        return my_prop;
    endfunction
    virtual task do_abstract_action();
        my_prop++;
    endtask
endclass
class Concrete implements MyInterface;
    int internal_value = 50;
    function new();
        internal_value = 51;
    endfunction
    virtual function int get_value();
        return internal_value;
    endfunction
    virtual task do_action();
        internal_value = internal_value + 1;
    endtask
endclass
class ConcreteDerivedIface implements DerivedInterface;
    int val = 100;
    function new();
        val = 101;
    endfunction
    virtual function int get_value();
        return val;
    endfunction
    virtual task do_action();
        val++;
    endtask
    virtual function void another_method();
        val += 10;
    endfunction
endclass
class ConcreteMulti implements MyInterface, MyInterface2;
    int multi_val = 300;
    function new();
        multi_val = 301;
    endfunction
    virtual function int get_value();
        return multi_val;
    endfunction
    virtual function int get_value_offset(int offset);
        return multi_val + offset;
    endfunction
    virtual task do_action();
        multi_val++;
    endtask
endclass
virtual class ConstraintClass;
    rand int x;
    rand int y;
    rand int z;
    static rand int static_rand_var;
    constraint c1          { x < 10;  }
    static constraint s_c  { static_rand_var == 20; }
    constraint i_c         { x + y == 15; }
    constraint f_c         { x != y; }
    pure constraint pure_c;
    extern constraint extern_c;
    extern static constraint static_extern_c;
    pure static constraint pure_static_c;
    function new();
    endfunction
    function void set_constraint_mode_method(bit on_ff);
        this.constraint_mode(on_ff);
    endfunction
    function void use_srandom(int seed);
        this.srandom(seed);
    endfunction
    function bit use_randomize();
        return this.randomize();
    endfunction
    function string get_randstate_method();
        return this.get_randstate();
    endfunction
endclass
constraint ConstraintClass::extern_c {
    z > 10;
    z < 30;
}
static constraint ConstraintClass::static_extern_c {
    ConstraintClass::static_rand_var != 10;
}
class DerivedConstraintClass extends ConstraintClass;
    constraint pure_c { y != z; x != z; }
    static constraint pure_static_c { ConstraintClass::static_rand_var inside {[1:10]}; }
    constraint i_c {
        x + y + z == 50;
    }
    constraint extern_c {
        z < 25;
    }
    function new();
    endfunction
endclass
class DerivedConstraintClassNoStaticMatch extends ConstraintClass;
    static constraint pure_static_c { ConstraintClass::static_rand_var inside {[1:10]}; }
    constraint pure_c { 1; }
    function new();
    endfunction
endclass
class DerivedConstraintClassInitialOverride extends ConstraintClass;
    constraint i_c { x + y == 100; }
    constraint pure_c { 1; }
    static constraint pure_static_c { 1; }
    function new();
    endfunction
endclass
class DerivedConstraintClassFinalOverride extends ConstraintClass;
    constraint f_c { x == y; }
    constraint pure_c { 1; }
    static constraint pure_static_c { 1; }
    function new();
    endfunction
endclass
class DerivedConstraintClassExtendsOverride extends ConstraintClass;
    constraint c1 { x > 5; }
    constraint pure_c { 1; }
    static constraint pure_static_c { 1; }
    function new();
    endfunction
endclass
class ConstraintNoExternDef;
    extern constraint my_extern_const;
    function new();
    endfunction
endclass
constraint ConstraintNoExternDef::my_extern_const { }
virtual class ConstraintNoPureDef;
    pure constraint my_pure_const;
    function new();
    endfunction
endclass
virtual class ConstraintPureWithBody;
    pure constraint my_pure_const;
    function new();
    endfunction
endclass
class Qualified;
    static int s_count = 100;
    local int l_val  = 20;
    protected int p_val = 30;
    const int C_VAL = 40;
    rand int r_val;
    randc int rc_val;
    function new();
        r_val = 0;
        rc_val = 0;
    endfunction
    function int get_l_val();
        return l_val;
    endfunction
    function int get_p_val();
        return p_val;
    endfunction
    function int get_c_val();
        return C_VAL;
    endfunction
    constraint c_r_val  { r_val  inside {[0:99]}; }
    constraint c_rc_val { rc_val inside {[0:9]};  }
    function void pre_randomize();
    endfunction
    function void post_randomize();
    endfunction
    function void set_rand_mode(bit on_ff);
        this.rand_mode(on_ff);
    endfunction
    function void use_srandom(int seed);
        this.srandom(seed);
    endfunction
endclass
class MyGeneric #(parameter type T = int, parameter int SIZE = 8);
    T data_arr [SIZE];
    function new();
    endfunction
    function void set_val(int idx, T val);
        if (idx >= 0 && idx < SIZE) begin
            data_arr[idx] = val;
        end
    endfunction
    function T get_val(int idx);
        if (idx >= 0 && idx < SIZE) begin
            return data_arr[idx];
        end else begin
            return '0;
        end
    endfunction
endclass
class GenericWithError #(parameter int P = 10);
    int data = P;
    function new();
        data = P;
    endfunction
    function int get_data();
        return data;
    endfunction
endclass
class BuiltInMethodClass;
    rand int r_var;
    function new();
    endfunction
    function void pre_randomize();
    endfunction
    function void post_randomize();
    endfunction
    function void set_state(string state);
        this.set_randstate(state);
    endfunction
    function void set_rand_mode(bit on);
        this.rand_mode(on);
    endfunction
    function void set_constraint_mode(bit on);
        this.constraint_mode(on);
    endfunction
    function void use_srandom(int seed);
        this.srandom(seed);
    endfunction
    function bit use_randomize();
        return this.randomize();
    endfunction
    function string get_randstate_method();
        return this.get_randstate();
    endfunction
endclass
module class_basic_properties(
    input  logic en,
    output logic [31:0] output_data
);
    Basic basic_inst;
    always_comb begin
        if (en) begin
            basic_inst = new();
            output_data = (basic_inst != null) ? basic_inst.getData() : 0;
        end else begin
            basic_inst = null;
            output_data = 0;
        end
    end
endmodule
module class_qualified_properties(
    input  logic clk,
    input  logic reset,
    input  logic go,
    input  int   srandom_seed,
    input  bit   rand_mode_on,
    output logic [31:0] rand_out,
    output logic [31:0] randc_out,
    output logic [31:0] static_out,
    output logic [31:0] const_out,
    output logic [31:0] local_out,
    output logic [31:0] protected_out
);
    Qualified qualified_inst;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            qualified_inst   = null;
            rand_out         <= 0;
            randc_out        <= 0;
            static_out       <= 0;
            const_out        <= 0;
            local_out        <= 0;
            protected_out    <= 0;
        end else begin
            if (qualified_inst == null)
                qualified_inst = new();
            static_out    <= Qualified::s_count;
            const_out     <= qualified_inst.get_c_val();
            local_out     <= qualified_inst.get_l_val();
            protected_out <= qualified_inst.get_p_val();
            if (go) begin
                qualified_inst.set_rand_mode(rand_mode_on);
                qualified_inst.use_srandom(srandom_seed);
            end
            rand_out  <= qualified_inst.r_val;
            randc_out <= qualified_inst.rc_val;
        end
    end
endmodule
module class_inheritance_ctor(
    input  logic en,
    input  int   base_d_in,
    input  int   derived_d_in,
    input  int   extends_args_no_super_d_in,
    input  int   invalid_default_req_arg_in,
    input  int   invalid_default_dd_in,
    output logic [31:0] derived_out,
    output logic [31:0] auto_ctor_out,
    output logic [31:0] extends_args_no_super_out,
    output logic [31:0] extends_args_super_out,
    output logic [31:0] invalid_extends_default_out,
    output logic        extends_args_no_super_inst_en,
    output logic        extends_args_super_inst_en,
    output logic        invalid_extends_default_inst_en
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
module class_interfaces(
    input  logic en,
    input  logic enable_action,
    input  int   multi_offset,
    output logic [31:0] interface_result,
    output logic [31:0] multi_interface_result_val,
    output logic [31:0] multi_interface_result_offset,
    output logic [31:0] derived_iface_result,
    output logic [31:0] diamond_iface_result,
    output logic [31:0] non_abstract_incomplete_prop,
    output logic        non_abstract_incomplete_inst_en,
    output logic        concrete_inst_en,
    output logic        concrete_derived_iface_inst_en,
    output logic        concrete_multi_inst_en,
    output logic        diamond_impl_inst_en
);
    Concrete              concrete_inst;
    ConcreteDerivedIface  concrete_derived_iface_inst;
    ConcreteMulti         concrete_multi_inst;
    InterfaceDiamondImpl  diamond_impl_inst;
    DerivedNonAbstractIncomplete non_abstract_incomplete_inst;
    always_comb begin
        if (en) begin
            concrete_inst             = new();
            concrete_derived_iface_inst = new();
            concrete_multi_inst       = new();
            diamond_impl_inst         = new();
            non_abstract_incomplete_inst = new();
            concrete_inst_en                = 1;
            concrete_derived_iface_inst_en  = 1;
            concrete_multi_inst_en          = 1;
            diamond_impl_inst_en            = 1;
            non_abstract_incomplete_inst_en = 1;
            interface_result = concrete_inst.get_value();
            derived_iface_result = concrete_derived_iface_inst.get_value();
            if (enable_action)
                concrete_derived_iface_inst.another_method();
            multi_interface_result_val    = concrete_multi_inst.get_value();
            multi_interface_result_offset = concrete_multi_inst.get_value_offset(multi_offset);
            diamond_iface_result          = diamond_impl_inst.common_method();
            non_abstract_incomplete_prop  = non_abstract_incomplete_inst.get_my_prop();
            if (enable_action) begin
                concrete_inst.do_action();
                concrete_derived_iface_inst.do_action();
                concrete_multi_inst.do_action();
                non_abstract_incomplete_inst.do_abstract_action();
            end
        end else begin
            concrete_inst = null;
            concrete_derived_iface_inst = null;
            concrete_multi_inst = null;
            diamond_impl_inst = null;
            non_abstract_incomplete_inst = null;
            concrete_inst_en                = 0;
            concrete_derived_iface_inst_en  = 0;
            concrete_multi_inst_en          = 0;
            diamond_impl_inst_en            = 0;
            non_abstract_incomplete_inst_en = 0;
            interface_result = 0;
            multi_interface_result_val = 0;
            multi_interface_result_offset = 0;
            derived_iface_result = 0;
            diamond_iface_result = 0;
            non_abstract_incomplete_prop = 0;
        end
    end
endmodule
module class_constraints(
    input  logic en,
    input  logic rnd_en,
    input  logic const_mode_en,
    input  int   srandom_seed,
    input  logic [31:0] static_var_in,
    output logic [31:0] x_out,
    output logic [31:0] y_out,
    output logic [31:0] z_out,
    output logic [31:0] static_var_out,
    output logic        rand_success,
    output logic        derived_rand_success,
    output logic [31:0] derived_x_out,
    output logic [31:0] derived_y_out,
    output logic [31:0] derived_z_out,
    output logic [31:0] pure_static_var_out,
    output logic [31:0] derived_static_mismatch_out,
    output logic        no_extern_def_inst_en,
    output logic        no_pure_def_inst_en,
    output logic        pure_with_body_inst_en,
    output logic        derived_static_mismatch_inst_en,
    output logic        initial_override_inst_en,
    output logic        final_override_inst_en,
    output logic        extends_override_inst_en,
    output logic        derived_constraint_inst_en
);
    DerivedConstraintClass             derived_constraint_inst;
    DerivedConstraintClassNoStaticMatch derived_static_mismatch_inst;
    DerivedConstraintClassInitialOverride initial_override_inst;
    DerivedConstraintClassFinalOverride   final_override_inst;
    DerivedConstraintClassExtendsOverride extends_override_inst;
    ConstraintNoExternDef  no_extern_def_inst;
    ConstraintNoPureDef    no_pure_def_inst;
    ConstraintPureWithBody pure_with_body_inst;
    bit success_flag;
    always_comb begin
        if (en) begin
            ConstraintClass::static_rand_var = static_var_in;
            no_extern_def_inst   = new();
            derived_static_mismatch_inst = new();
            initial_override_inst = new();
            final_override_inst   = new();
            extends_override_inst = new();
            derived_constraint_inst = new();
            no_extern_def_inst_en          = 1;
            derived_static_mismatch_inst_en = 1;
            initial_override_inst_en       = 1;
            final_override_inst_en         = 1;
            extends_override_inst_en       = 1;
            derived_constraint_inst_en     = 1;
            no_pure_def_inst_en            = 0;
            pure_with_body_inst_en         = 0;
            static_var_out            = ConstraintClass::static_rand_var;
            pure_static_var_out       = ConstraintClass::static_rand_var;
            derived_static_mismatch_out = ConstraintClass::static_rand_var;
            if (rnd_en) begin
                derived_constraint_inst.set_constraint_mode_method(const_mode_en);
                derived_constraint_inst.use_srandom(srandom_seed);
                success_flag = derived_constraint_inst.use_randomize();
                derived_x_out = derived_constraint_inst.x;
                derived_y_out = derived_constraint_inst.y;
                derived_z_out = derived_constraint_inst.z;
                derived_rand_success = success_flag;
                x_out = derived_x_out;
                y_out = derived_y_out;
                z_out = derived_z_out;
                rand_success = success_flag;
            end else begin
                x_out = 0;
                y_out = 0;
                z_out = 0;
                rand_success = 0;
                derived_x_out = 0;
                derived_y_out = 0;
                derived_z_out = 0;
                derived_rand_success = 0;
            end
        end else begin
            derived_constraint_inst = null;
            no_extern_def_inst      = null;
            derived_static_mismatch_inst = null;
            initial_override_inst   = null;
            final_override_inst     = null;
            extends_override_inst   = null;
            derived_static_mismatch_inst_en = 0;
            initial_override_inst_en       = 0;
            final_override_inst_en         = 0;
            extends_override_inst_en       = 0;
            derived_constraint_inst_en     = 0;
            no_extern_def_inst_en          = 0;
            no_pure_def_inst_en            = 0;
            pure_with_body_inst_en         = 0;
            x_out = 0;
            y_out = 0;
            z_out = 0;
            static_var_out = 0;
            pure_static_var_out = 0;
            rand_success = 0;
            derived_x_out = 0;
            derived_y_out = 0;
            derived_z_out = 0;
            derived_rand_success = 0;
            derived_static_mismatch_out = 0;
        end
    end
endmodule
module generic_class_specialization(
    input  logic en,
    input  logic [7:0]  val1_in,
    input  logic [31:0] val2_in,
    output logic [7:0]  data_out_gen1,
    output logic [31:0] data_out_gen2,
    output logic [31:0] data_out_gen_default,
    output logic [31:0] invalid_gen_out,
    output logic        invalid_inst_en
);
    MyGeneric #(.T(logic [7:0]), .SIZE(4)) gen1;
    MyGeneric #(int, 16) gen2;
    MyGeneric #() gen_default;
    GenericWithError #(.P(123)) invalid_inst;
    always_comb begin
        if (en) begin
            gen1 = new();
            gen2 = new();
            gen_default = new();
            invalid_inst = new();
            invalid_inst_en = 1;
            gen1.set_val(0, val1_in);
            data_out_gen1 = gen1.get_val(0);
            gen2.set_val(5, val2_in);
            data_out_gen2 = gen2.get_val(5);
            gen_default.set_val(0, $unsigned(val1_in));
            data_out_gen_default = gen_default.get_val(0);
            invalid_gen_out = invalid_inst.get_data();
        end else begin
            gen1 = null;
            gen2 = null;
            gen_default = null;
            invalid_inst = null;
            invalid_inst_en = 0;
            data_out_gen1 = 0;
            data_out_gen2 = 0;
            data_out_gen_default = 0;
            invalid_gen_out = 0;
        end
    end
endmodule
module abstract_final_classes(
    input  logic en,
    input  logic trigger_action,
    output logic [31:0] abstract_val,
    output logic [31:0] final_val,
    output logic [31:0] derived_prop_out,
    output logic        extends_final_inst_en,
    output logic        extends_interface_inst_en
);
    ConcreteDerived concrete_abstract_inst;
    CannotExtend    final_inst;
    ExtendsFinal    extends_final_inst;
    ExtendsInterface extends_interface_inst;
    always_comb begin
        if (en) begin
            concrete_abstract_inst = new();
            final_inst = new();
            extends_final_inst = new();
            extends_interface_inst = new();
            extends_final_inst_en    = 1;
            extends_interface_inst_en = 1;
            if (trigger_action)
                concrete_abstract_inst.do_abstract_action();
            abstract_val      = concrete_abstract_inst.get_val();
            derived_prop_out  = concrete_abstract_inst.derived_prop;
            final_val         = final_inst.get_data();
        end else begin
            concrete_abstract_inst = null;
            final_inst   = null;
            extends_final_inst = null;
            extends_interface_inst = null;
            extends_final_inst_en = 0;
            extends_interface_inst_en = 0;
            abstract_val = 0;
            final_val = 0;
            derived_prop_out = 0;
        end
    end
endmodule
module forward_typedef_module(
    input  logic en,
    input  int   value_in,
    output logic [31:0] data_out
);
    ForwardDeclaredClass inst;
    always_comb begin
        if (en) begin
            inst = new(value_in);
            data_out = inst.value;
        end else begin
            inst = null;
            data_out = 0;
        end
    end
endmodule
module cyclic_class_module(
    input  logic en,
    input  int   val_a_in,
    input  int   val_b_in,
    output logic [31:0] total_sum,
    output logic        inst_a_en,
    output logic        inst_b_en
);
    CyclicA inst_a;
    always_comb begin
        if (en) begin
            inst_a = new(val_a_in);
            inst_a_en = 1;
            inst_a.b_inst = new(val_b_in);
            inst_b_en = 1;
            inst_a.b_inst.a_inst = inst_a;
            total_sum = inst_a.a_prop + inst_a.b_inst.b_prop;
        end else begin
            inst_a = null;
            total_sum = 0;
            inst_a_en = 0;
            inst_b_en = 0;
        end
    end
endmodule
module implements_non_iface_module(
    input  logic en,
    output logic implements_non_class_inst_en
);
    ImplementsNonIfaceError implements_non_class_inst;
    always_comb begin
        if (en) begin
            implements_non_class_inst = new();
            implements_non_class_inst_en = 1;
        end else begin
            implements_non_class_inst = null;
            implements_non_class_inst_en = 0;
        end
    end
endmodule
module class_built_in_methods(
    input  logic  en,
    input  logic  do_randomize,
    input  logic  do_set_rand_state,
    input  string state_in,
    input  logic  rand_mode_on,
    input  logic  constraint_mode_on,
    input  int    srandom_seed,
    output logic [31:0] r_var_out,
    output string       get_state_out,
    output logic        randomize_success
);
    BuiltInMethodClass built_in_inst;
    bit success_flag;
    always_comb begin
        if (en) begin
            if (built_in_inst == null)
                built_in_inst = new();
            built_in_inst.set_rand_mode(rand_mode_on);
            built_in_inst.set_constraint_mode(constraint_mode_on);
            built_in_inst.use_srandom(srandom_seed);
            if (do_set_rand_state) begin
                built_in_inst.set_state(state_in);
                get_state_out = built_in_inst.get_randstate_method();
                r_var_out = built_in_inst.r_var;
                randomize_success = 0;
            end else if (do_randomize) begin
                success_flag = built_in_inst.use_randomize();
                r_var_out = built_in_inst.r_var;
                get_state_out = built_in_inst.get_randstate_method();
                randomize_success = success_flag;
            end else begin
                r_var_out = built_in_inst.r_var;
                get_state_out = built_in_inst.get_randstate_method();
                randomize_success = 0;
            end
        end else begin
            built_in_inst = null;
            r_var_out = 0;
            get_state_out = "";
            randomize_success = 0;
        end
    end
endmodule

interface MyInterface (input logic clk);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
module ModuleWithInterface (
    input logic clk_in,
    output logic valid_out
);
    MyInterface my_if (clk_in);
    assign my_if.req = 1'b1;
    assign valid_out = my_if.valid;
endmodule
module ModuleWithStruct (
    input logic [7:0] data_in,
    output int sum_out
);
    typedef struct {
        int field_a;
        logic [7:0] field_b;
        logic field_c;
    } MyStruct;
    MyStruct struct_var;
    int local_sum;
    always_comb begin
        struct_var.field_a = $unsigned(data_in);
        struct_var.field_b = data_in;
        struct_var.field_c = |data_in;
        local_sum = struct_var.field_a + $unsigned(struct_var.field_b);
        sum_out = local_sum;
    end
endmodule
module ModuleWithUnion (
    input logic select,
    input int val_int,
    input byte val_byte,
    output int out_int
);
    typedef union {
        int u_field_int;
        byte u_field_byte;
    } MyUnion;
    MyUnion union_var;
    int result_int;
    always_comb begin
        if (select) begin
            union_var.u_field_int = val_int;
        end else begin
            union_var.u_field_byte = val_byte;
        end
        result_int = union_var.u_field_int;
        out_int = result_int;
    end
endmodule
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
class ParamClass #(parameter int SIZE = 8);
    logic [SIZE-1:0] data_array;
    int param_member;
    function new(logic [SIZE-1:0] arr, int pm);
        data_array = arr;
        param_member = pm;
    endfunction
endclass
module ModuleWithParamClass (
    input int data_val,
    output int param_sum_out
);
    ParamClass #(16) param_instance_16;
    always_comb begin
        logic [15:0] temp_array_16;
        temp_array_16 = $unsigned(data_val);
        param_instance_16 = new(temp_array_16, data_val + 5);
        param_sum_out = param_instance_16.param_member + $unsigned(param_instance_16.data_array[0]);
    end
endmodule
class MySimpleClass;
    int member_int;
    logic member_logic;
    logic [63:0] member_wide;
    function new(int i, logic l, logic [63:0] w);
        member_int = i;
        member_logic = l;
        member_wide = w;
    endfunction
endclass
module ModuleWithClass (
    input logic in1,
    output logic out1
);
    MySimpleClass my_instance;
    always_comb begin
        my_instance = new(10, in1, 64'hFFFF_0000_FFFF_0000);
        out1 = my_instance.member_logic;
    end
endmodule

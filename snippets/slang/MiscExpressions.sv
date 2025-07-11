package my_package;
    parameter PKG_PARAM = 25;
endpackage
typedef logic [7:0] byte_t;
module MiscExpressions_NamedValue_Assignments (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [15:0] out_sum,
    output logic [7:0] out_param_val,
    output logic [7:0] out_const_var_val,
    output logic [7:0] out_enum_val
);
    parameter int PARAM_VAL = 10;
    localparam logic [7:0] CONST_PARAM = 5;
    const logic [7:0] CONST_VAR = 20;
    logic [7:0] local_var;
    enum { ENUM_VAL1 = 1, ENUM_VAL2 = 2 } enum_type;
    task automatic automatic_task;
        input logic [7:0] arg_a;
        input logic [7:0] arg_b;
        output logic [15:0] sum;
        automatic logic [7:0] auto_local_in_task;
        begin
            auto_local_in_task = arg_b;
            sum = arg_a + auto_local_in_task;
        end
    endtask
    always_comb begin
        logic [15:0] temp_sum;
        local_var = in_a;
        automatic_task(local_var, in_b, temp_sum);
        out_sum = temp_sum;
        out_param_val = PARAM_VAL;
        out_const_var_val = CONST_VAR;
        out_enum_val = ENUM_VAL1;
    end
endmodule
module MiscExpressions_HierarchicalValue (
    input logic [7:0] in_dummy,
    output logic [7:0] out_hier_param_pkg
);
    assign out_hier_param_pkg = my_package::PKG_PARAM;
endmodule
module MiscExpressions_DataType_TypeRef (
    input int in_int,
    input real in_real,
    input logic [3:0] in_logic,
    output real out_real,
    output int out_int,
    output byte_t out_cast_logic,
    output string out_type_name
);
    typedef struct packed {
        logic [3:0] addr;
        logic [7:0] data;
    } my_struct_t;
    always_comb begin
        out_real = real'(in_int);
        out_int = int'(in_real);
        out_cast_logic = byte_t'(in_logic);
        out_type_name = $typename(my_struct_t);
    end
endmodule
module MiscExpressions_Assertions (
    input bit clk,
    input bit a,
    input bit b,
    output bit out_s1_a_ok,
    output bit out_p1_ab_ok,
    output bit out_s1_b_ok,
    output bit out_p1_ab_named_ok,
    output bit out_p3_ok,
    output bit out_let_ab_ok,
    output bit out_p_seq_ok,
    output bit out_p_event_ok
);
    clocking cb @(posedge clk); endclocking
    sequence s1 (local input bit sig);
        @(posedge clk) sig ##1 !sig;
    endsequence
    property p1 (local input bit sig1, local input bit sig2);
        @(posedge clk) sig1 |-> ##[1:3] sig2;
    endproperty
    property p3 (local input bit sig = 1'b1);
        @(posedge clk) sig;
    endproperty
    property p_seq(sequence sq_arg);
        @(posedge clk) sq_arg;
    endproperty
    property p_event(event ev_formal);
        // slang does not support event variables in property/event context; replace with legal clocking event
        @(posedge clk) 1'b1;
    endproperty
    let my_let (bit X, bit Y) = X && Y;
    always_ff @(posedge clk) begin assert property (s1(a)); out_s1_a_ok = 1'b1; end
    always_ff @(posedge clk) begin assert property (p1(a, b)); out_p1_ab_ok = 1'b1; end
    always_ff @(posedge clk) begin assert property (s1(.sig(b))); out_s1_b_ok = 1'b1; end
    always_ff @(posedge clk) begin assert property (p1(.sig1(a), .sig2(b))); out_p1_ab_named_ok = 1'b1; end
    always_ff @(posedge clk) begin assert property (p3()); out_p3_ok = 1'b1; end
    always_ff @(posedge clk) begin assert property (@cb my_let(a, b)); out_let_ab_ok = 1'b1; end
endmodule
class MyRandClass_Dist;
    rand int rand_var_int;
    real rand_var_real;
    rand bit rand_var_bit;
    int c_min;
    int c_max;
    real c_real;
    constraint dist_constraints_int {
        rand_var_int dist { c_min := 10, c_max := 5, [c_min+1 : c_max-1] :/ 20 };
    }
    `ifdef SV_2023
    constraint dist_constraints_real {
        rand_var_real dist { [c_min : c_max] :/ 10.0, c_real := 5.0, 10.0 :/ 2.0 };
    }
    `endif
    constraint dist_constraints_bit {
        rand_var_bit dist { 0 := 1, 1 := 1 };
    }
    function new(int min, int max, real rv);
        this.c_min = min;
        this.c_max = max;
        this.c_real = rv;
    endfunction
endclass
module MiscExpressions_Dist_RandClass (
    input int in_min,
    input int in_max,
    input real in_real_val,
    output int out_rand_int,
    output real out_rand_real,
    output bit out_dist_ok
);
    MyRandClass_Dist rand_obj;
    int randomize_status;
    always_comb begin
        if (rand_obj == null) begin
            rand_obj = new(in_min, in_max, in_real_val);
        end else begin
            rand_obj.c_min = in_min;
            rand_obj.c_max = in_max;
            rand_obj.c_real = in_real_val;
        end
        randomize_status = rand_obj.randomize();
        out_rand_int = rand_obj.rand_var_int;
        `ifdef SV_2023
            out_rand_real = rand_obj.rand_var_real;
        `else
            out_rand_real = 0.0;
        `endif
        out_dist_ok = rand_obj.rand_var_bit;
    end
endmodule
module MiscExpressions_TaggedUnion (
    input byte in_u_byte,
    input int in_u_int,
    output bit out_union_ok,
    output int out_union_int
);
    typedef union tagged {
        byte b;
        int i;
        real r;
        void v;
    } my_tagged_union_t;
    my_tagged_union_t u_var;
    my_tagged_union_t u_int_var;
    const my_tagged_union_t const_u = tagged b 8'hAA;
    always_comb begin
        u_var = tagged b in_u_byte;
        u_int_var = tagged i in_u_int;
        out_union_int = u_int_var.i;
        out_union_ok = 1'b1;
    end
endmodule
module MiscExpressions_TaggedUnionParam (
    input logic in_dummy,
    output byte out_union_param_val
);
    typedef union tagged {
        byte b;
        int i;
    } param_union_t;
    parameter param_union_t p_u = tagged b 8'hFF; 
    assign out_union_param_val = p_u.b; 
endmodule
module MiscExpressions_AssignmentErrors (
    input wire logic in_wire_input,
    input bit in_bit_input,
    input int in_int_input,
    input bit in_auto_bit_input, 
    input logic clk_err,
    output logic out_placeholder,
    output logic out_nonblocking_dummy
);
    logic net_var; // changed from 'wire logic' to 'logic' for procedural assignment
    int var_assignable; // new variable to replace illegal const assignment
    const int const_var = 5;
    always_comb begin
        net_var = in_bit_input; // now legal, as net_var is logic
        var_assignable = in_int_input; // legal assignment
    end
    // Removed illegal assignment to const_var
    always @(posedge clk_err) begin
        automatic bit auto_var; 
        auto_var = in_auto_bit_input; // use blocking assignment for automatic variable
    end
    assign out_placeholder = 1'b1;
    assign out_nonblocking_dummy = 1'b0;
endmodule
module MiscExpressions_ValueRange (
    input logic [15:0] in_vector,
    output logic [7:0] out_slice
);
    always_comb begin
        out_slice = in_vector[7:0];
    end
endmodule
class MyClass;
    int data;
    function new(); endfunction
    function MyClass copy();
        MyClass new_obj = new();
        new_obj.data = this.data;
        return new_obj;
    endfunction
endclass
module MiscExpressions_CopyClass (
    input int in_data,
    output int out_copied_data
);
    MyClass original_obj;
    MyClass copied_obj;
    always_comb begin
        if (original_obj == null) begin
            original_obj = new();
        end
        original_obj.data = in_data;
        copied_obj = original_obj.copy(); // fixed: use method call, not type name
        if (copied_obj != null) begin
            out_copied_data = copied_obj.data;
        end else begin
            out_copied_data = 0;
        end
    end
endmodule
module MiscExpressions_CopyClassNewCopy (
    input int in_data,
    output int out_copied_data
);
    MyClass copied_obj;
    always_comb begin
        copied_obj = new(); // fixed: use legal constructor
        if (copied_obj != null) begin
            copied_obj.data = in_data;
            out_copied_data = copied_obj.data;
        end else begin
            out_copied_data = 0;
        end
    end
endmodule
module MiscExpressions_ConstEval (
    input int in_dummy,
    output int out_size
);
    class MyType;
        int x;
    endclass
    parameter type T = MyType;
    parameter int SIZE_OF_T = $bits(T); 
    assign out_size = SIZE_OF_T;
endmodule
module MiscExpressions_ClockVar_Binding (
    input logic clk_in,
    input logic in_data,
    output logic clk_out_port,
    output logic out_data_read_input,
    output logic out_data_read_output_dummy
);
    logic clock_var_output;
    clocking cb @(posedge clk_in);
        output clock_var_output;
        input in_data;
    endclocking
    assign clk_out_port = clock_var_output; 
    assign out_data_read_input = cb.in_data;
    assign out_data_read_output_dummy = 1'b0;
    always_ff @(cb) begin
        cb.clock_var_output <= in_data;
    end
endmodule
module MiscExpressions_ClockingEventExpr (
    input logic clk,
    input int in_value,
    output int out_sampled_value
);
    clocking cb @(posedge clk); endclocking
    always_ff @(cb) begin
        out_sampled_value = $sampled(in_value); 
    end
endmodule
module mod_simple (input wire in, output wire out);
    assign out = in;
endmodule
module MiscExpressions_ArrayInstanceName (
    input wire in_dummy,
    output wire out_dummy
);
    mod_simple inst_array[2:0](.in(), .out()); // connect all ports to avoid unconnected-port warnings
    wire dummy_in;
    wire dummy_out;
    assign dummy_in = in_dummy;
    assign inst_array[1].in = dummy_in; 
    assign dummy_out = inst_array[1].out; 
    assign out_dummy = dummy_out;
endmodule

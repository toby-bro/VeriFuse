module ModuleBasic (
    input  logic a,
    input  int   b,
    output logic out_a,
    output int   out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule
module ModuleHierarchy_High #(parameter int SEL_PARAM = 6) (
    input  int          sel_in,
    input  logic [3:0]  data_in,
    output logic [7:0]  data_out
);
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (sel_in),
        .out_a  (),
        .out_b  (/*unused*/ )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data)
        );
    end else begin : gen_low
        int low_data;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in;
        assign sub_in = data_in[i*2 +: 2];
        int temp_int;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in)),
            .out_a  (),
            .out_b  (temp_int)
        );
        assign data_out[i*4 +: 4] = temp_int[3:0];
    end
endmodule
module ModuleHierarchy_Low #(parameter int SEL_PARAM = 5) (
    input  int          sel_in,
    input  logic [3:0]  data_in,
    output logic [7:0]  data_out
);
    ModuleBasic m1 (
        .a     (1'b1),
        .b     (sel_in),
        .out_a (),
        .out_b (/*unused*/ )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data;
        ModuleBasic m_high (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (high_data)
        );
    end else begin : gen_low
        int low_data;
        ModuleBasic m_low (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (low_data)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in;
        assign sub_in = data_in[i*2 +: 2];
        int temp_int;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in)),
            .out_a  (),
            .out_b  (temp_int)
        );
        assign data_out[i*4 +: 4] = temp_int[3:0];
    end
endmodule
module ModuleTypes (
    input  int          in_val,
    input  logic [7:0]  packed_data,
    output int          out_val,
    output bit  [15:0]  unpacked_data_out
);
    typedef struct packed {
        logic a;
        int   b;
    } packed_s;
    packed_s ps;
    typedef union packed {
        int i;
        int j;
    } unpacked_u;
    unpacked_u uu;
    typedef enum { IDLE, RUNNING, DONE } state_e;
    state_e current_state = IDLE;
    typedef bit [15:0] my_word_t;
    my_word_t mw;
    parameter type DATA_T = int;
    DATA_T param_var;
    always_comb begin
        ps.a = packed_data[0];
        ps.b = in_val;
        unpacked_data_out[7:0]  = packed_data;
        uu.i                    = in_val + 1;
        unpacked_data_out[15:8] = uu.j[7:0];
        out_val   = in_val + ps.b + int'(current_state);
        param_var = in_val;
        out_val   = out_val + param_var;
        mw                 = in_val;
        unpacked_data_out  = unpacked_data_out ^ mw;
    end
endmodule
module ModuleSubroutines (
    input  int in1,
    input  int in2,
    output int out_func,
    output int out_task
);
    function automatic int add_func (input int a, input int b);
        return a + b;
    endfunction
    task automatic multiply_task (input int a, input int b, output int result);
        result = a * b;
    endtask
    assign out_func = add_func(in1, in2);
    always_comb begin
        int temp_res;
        multiply_task(in1, in2, temp_res);
        out_task = temp_res;
    end
endmodule
(* my_module_attr = "Module Attribute Value" *)
module ModuleWithAttributes (
    (* my_port_attr *) input  bit attr_in,
    output bit attr_out
);
    (* my_param_attr *) parameter int P_ATTR = 5;
    (* my_var_attr = 123 *) logic var_attr;
    (* my_func_attr *) function bit process_attr (bit i);
        return i;
    endfunction
    assign var_attr  = attr_in;
    assign attr_out  = process_attr(var_attr);
endmodule
module ModuleClassRand (
    input  int class_in,
    output int class_out
);
    class MyClass;
        rand  int rand_prop;
        randc int randc_prop;
        int       normal_prop;
        function new ();
            rand_prop   = 1;
            randc_prop  = 2;
            normal_prop = 3;
        endfunction
        function int sum_props ();
            return rand_prop + randc_prop + normal_prop;
        endfunction
        constraint simple_constr { rand_prop > 0; }
    endclass
    MyClass obj;
    always_comb begin
        if (obj == null)
            obj = new();
        if (obj != null)
            class_out = obj.sum_props() + class_in;
        else
            class_out = 0;
    end
endmodule
package my_package;
    parameter int PKG_PARAM = 100;
    function automatic bit pkg_func (bit i);
        return !i;
    endfunction
endpackage
module ModulePackageEscaped (
    input  bit pkg_in,
    output bit pkg_out
);
    import my_package::*;
    localparam int LP_PKG = PKG_PARAM;
    logic \escaped_name ;
    assign \escaped_name  = pkg_in;
    assign pkg_out        = pkg_func(\escaped_name );
endmodule
module ModuleOtherSymbols (
    input  logic       clk,
    input  int         order_in,
    input  logic [7:0] var1_in,
    input  logic [7:0] var2_in,
    output int         order_out,
    output wire [7:0]  var1_out,
    output wire [7:0]  var2_out
);
    wire [7:0] var1;
    wire [7:0] var2;
    assign var1 = var1_in;
    assign var2 = var2_in;
    covergroup cg @(posedge clk);
        cp : coverpoint order_in;
    endgroup
    cg cg_inst = new();
    assign var1_out  = var1;
    assign var2_out  = var2;
    assign order_out = {var2, var1};
endmodule
interface my_interface;
    logic clk;
    logic en;
    logic data;
    modport master ( output clk, output en, input  data );
    modport slave  ( input  clk, input  en, output data );
    clocking cb @(posedge clk);
        input  en;
        input  data;
    endclocking
endinterface
module ModuleInterfaces (
    input  logic master_clk,
    input  logic master_en,
    input  logic slave_data_in,
    output logic slave_data_out,
    input  logic dummy_in,
    output logic dummy_out
);
    my_interface intf();
    assign intf.clk  = master_clk;
    assign intf.en   = master_en;
    assign intf.data = slave_data_in;
    assign slave_data_out = intf.data;
    virtual my_interface vif_master;
    always_comb begin
        vif_master = intf;
        dummy_out  = vif_master.cb.en;
    end
endmodule
module ModuleArraysAndMore (
    input  int          array_in,
    input  logic [7:0]  packed_arr_in,
    output int          array_out,
    output real         real_out,
    output shortreal    shortreal_out
);
    logic  [3:0] packed_array [1:0];
    int          unpacked_array [2];
    int          dynamic_array [];
    int          associative_array [*];
    int          queue_var [$];
    string       string_var;
    event        event_var;
    real         real_var;
    shortreal    shortreal_var;
    always_comb begin
        automatic int sum;
        int idx;
        packed_array[0] = packed_arr_in[3:0];
        packed_array[1] = packed_arr_in[7:4];
        unpacked_array[0] = array_in;
        unpacked_array[1] = array_in + 1;
        dynamic_array = new[3];
        dynamic_array[0] = unpacked_array[0];
        dynamic_array[1] = unpacked_array[1];
        dynamic_array[2] = int'(packed_array[0]);
        associative_array[10]   = array_in;
        associative_array["key"] = array_in + 2;
        queue_var.push_back(array_in);
        queue_var.push_front(array_in - 1);
        sum = 0;
        if (queue_var.size() > 0)
            sum = queue_var.pop_front();
        if (queue_var.size() > 0)
            sum += queue_var.pop_back();
        string_var    = "hello";
        real_var      = $itor(array_in) + 0.5;
        shortreal_var = real_var;
        real_out      = real_var;
        shortreal_out = shortreal_var;
        foreach (dynamic_array[idx])
            sum += dynamic_array[idx];
        array_out = sum;
    end
endmodule
module ModuleForwardTypedefs (
    input  logic dummy_in,
    output logic dummy_out
);
    typedef class ForwardedClass;
    class ForwardedClass;
        int val;
        function new (int v); val = v; endfunction
    endclass
    ForwardedClass cls_h;
    always_comb begin
        cls_h = new(10);
        if (cls_h != null)
            dummy_out = cls_h.val > 0;
        else
            dummy_out = dummy_in;
    end
endmodule
module ModuleChecker (
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic checker_out
);
    checker my_checker (input logic clk_i, input logic a_i, input logic b_i);
        logic local_var;
        sequence s_check;
            @(posedge clk_i) a_i ##[1:2] b_i;
        endsequence
        property p_check;
            @(posedge clk_i) s_check |=> b_i;
        endproperty
        assert property (p_check);
        always_comb begin
            local_var = a_i ^ b_i;
        end
    endchecker
    my_checker checker_inst ( .clk_i(clk), .a_i(a), .b_i(b) );
    assign checker_out = a & b;
endmodule
module ModuleClocking (
    input  logic clk_in,
    input  logic data_in,
    output logic data_out
);
    clocking cb @(posedge clk_in);
        input  data_in;
        output data_out;
    endclocking
    always_ff @(cb) begin
        data_out <= cb.data_in;
    end
endmodule
module ModuleLet (
    input  int a_in,
    input  int b_in,
    output int c_out
);
    let my_add (x, y) = x + y;
    assign c_out = my_add(a_in, b_in);
endmodule

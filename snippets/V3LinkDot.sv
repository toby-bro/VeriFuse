module BasicModule (
    input wire [7:0] in_data,
    input wire in_valid,
    output wire [7:0] out_data,
    output wire out_valid
);
    parameter int WIDTH = 8;
    localparam int ZERO = 0;
    reg [WIDTH-1:0] internal_reg;
    wire [WIDTH-1:0] internal_wire;
    assign internal_wire = in_data + ZERO;
    always_comb begin
        internal_reg = internal_wire;
    end
    assign out_data = internal_reg;
    assign out_valid = in_valid;
endmodule
module ProceduralModule (
    input wire clk,
    input wire reset,
    input wire [3:0] p_in,
    output reg [3:0] p_out
);
    always @(posedge clk or posedge reset) begin : clocked_block
        reg [3:0] clocked_reg;
        if (reset) begin : reset_block
            clocked_reg = 4'b0;
            p_out = 4'b0;
        end else begin : operation_block
            clocked_reg = p_in;
            p_out = clocked_reg;
        end
    end
endmodule
package MyPackage;
    parameter int PKG_WIDTH = 16;
    static int pkg_var = 5;
    typedef enum { RED, GREEN, BLUE } color_e;
    function automatic int pkg_func (int val);
        return val + PKG_WIDTH;
    endfunction
    function automatic int get_pkg_var();
        return pkg_var;
    endfunction
    export *;
endpackage
import MyPackage::PKG_WIDTH;
module PackageModule (
    input wire [PKG_WIDTH-1:0] pkg_in,
    output wire [PKG_WIDTH-1:0] pkg_out,
    output wire [31:0] func_out,
    output wire [31:0] pkg_var_out,
    output wire [31:0] color_code_out
);
    import MyPackage::*;
    color_e current_color;
    assign pkg_out = pkg_in;
    assign func_out = pkg_func(pkg_in);
    always_comb begin
       MyPackage::pkg_var = 10;
       current_color = RED;
       color_code_out = current_color;
    end
    assign pkg_var_out = get_pkg_var();
endmodule
interface SimpleIface # (parameter int IFACE_WIDTH = 8) (input wire clk);
    logic [IFACE_WIDTH-1:0] data;
    logic valid;
    modport controller (output data, output valid, input clk);
    modport peripheral (input data, input valid, input clk);
endinterface
module InterfaceModule (
    SimpleIface.controller control_if,
    input wire [7:0] if_in,
    output wire if_out
);
    assign control_if.data = if_in;
    assign control_if.valid = if_in > 0;
    assign if_out = control_if.data[0];
endmodule
module ClockingModule (
    input wire clk,
    input wire data_in,
    output reg data_out
);
    clocking cb @(posedge clk);
        input data_in;
        output data_out;
    endclocking
    always @(cb) begin
        data_out <= cb.data_in;
    end
    always @(cb.default_event) begin
    end
endmodule
module ForeachModule (
    input wire [7:0] in_array [0:3],
    output reg [7:0] out_sum,
    output reg [7:0] out_sum_idx
);
    always_comb begin
        out_sum = 0;
        foreach(in_array[i]) begin
            out_sum = out_sum + in_array[i];
        end
    end
     always_comb begin
        out_sum_idx = 0;
        foreach (in_array[int idx]) begin
           out_sum_idx = out_sum_idx + in_array[idx];
        end
    end
endmodule
module TypedefModule (
    input wire [PKG_WIDTH-1:0] in_val,
    output wire [PKG_WIDTH-1:0] out_val,
    output wire [31:0] color_code_out
);
    import MyPackage::*;
    MyPackage::color_e status_color;
    parameter type ValueType = logic [PKG_WIDTH-1:0];
    ValueType internal_value;
    assign internal_value = in_val;
    assign out_val = internal_value;
    always_comb begin
       status_color = GREEN;
       color_code_out = status_color;
    end
endmodule
module DpiExportModule (
    input int dpi_in,
    output int dpi_out
);
    function automatic int my_exported_func (input int val);
        return val * 2;
    endfunction
    export "DPI-C" function my_exported_func;
    always_comb begin
        dpi_out = my_exported_func(dpi_in);
    end
endmodule
typedef class FwdClass;
class BaseClass # (parameter int P = 1);
    rand int base_var;
    static int static_base_var = 0;
    protected int protected_base_var = 0;
    function new();
        base_var = 0;
    endfunction
    virtual function int get_base_var();
        return base_var;
    endfunction
    static function int get_static_base_var();
        return static_base_var;
    endfunction
    pure virtual function int pure_func();
    virtual task base_task(input int val);
    endtask
    constraint base_constr {
        base_var > 0;
    }
    constraint pure_constr { pure; };
endclass
class FwdClass;
    int fwd_var = 100;
    function new();
    endfunction
    function int get_fwd_var();
        return fwd_var;
    endfunction
endclass
class DerivedClass # (parameter int P_VAL = 2) extends BaseClass#(P_VAL);
    randc int derived_var;
    SimpleIface if_handle;
    FwdClass fwd_obj;
    constraint derived_constr {
        derived_var inside {[10:20]};
        pure_constr;
        base_constr;
        if (fwd_obj != null) fwd_obj.fwd_var > 50;
        solve derived_var before base_var;
    }
    function new(int b_val, SimpleIface ifc);
        super.new();
        this.base_var = b_val;
        this.derived_var = b_val + 5;
        this.if_handle = ifc;
        fwd_obj = new();
    endfunction
    virtual function int pure_func();
        return derived_var;
    endfunction
    virtual function int get_base_var();
        return super.get_base_var();
    endfunction
    virtual task derived_task(input int val);
       super.base_task(val);
    endtask
    function void my_randomize_method();
        randomize(local::derived_var) with { derived_var < 15; };
    endfunction
    function int get_fwd_var_from_obj();
        return fwd_obj.get_fwd_var();
    endfunction
    function int access_protected();
        return this.protected_base_var;
    endfunction
    function automatic int get_all_base_vars();
       return this.base_var + this.protected_base_var;
    endfunction
endclass
module ClassModule (
    input wire clk,
    input wire [7:0] class_in,
    SimpleIface if_instance,
    input wire task_val_in,
    output wire class_out,
    output wire [31:0] base_var_out,
    output wire [31:0] pure_func_out,
    output wire [31:0] fwd_var_out,
    output wire [31:0] static_var_out,
    output wire [31:0] all_base_vars_out,
    output wire [31:0] protected_access_out
);
    DerivedClass#(10) my_derived_obj;
    always @(posedge clk) begin
        if (my_derived_obj == null) begin
             my_derived_obj = new(class_in, if_instance);
        end
        if (my_derived_obj != null) begin
           my_derived_obj.my_randomize_method();
           my_derived_obj.derived_task(task_val_in);
        end
    end
    always_comb begin
        if (my_derived_obj != null) begin
            class_out = my_derived_obj.if_handle.valid;
            base_var_out = my_derived_obj.get_base_var();
            pure_func_out = my_derived_obj.pure_func();
            fwd_var_out = my_derived_obj.get_fwd_var_from_obj();
            all_base_vars_out = my_derived_obj.get_all_base_vars();
            protected_access_out = my_derived_obj.access_protected();
        end else begin
            class_out = 1'b0;
            base_var_out = 32'b0;
            pure_func_out = 32'b0;
            fwd_var_out = 32'b0;
            all_base_vars_out = 32'b0;
            protected_access_out = 32'b0;
        end
        static_var_out = DerivedClass#(10)::get_static_base_var();
    end
endmodule
module ParameterizedInnerModule # (parameter int INNER_PARAM = 1);
    input wire inner_in;
    output wire inner_out;
    reg [31:0] inner_reg;
    assign inner_out = inner_reg[0];
    always @* begin
        inner_reg = inner_in + INNER_PARAM;
    end
endmodule
module ParameterizedHierarchicalModule (
    input wire outer_in,
    output wire outer_out,
    output wire [31:0] internal_access_out
);
    ParameterizedInnerModule #(5) inner_inst (.inner_in(outer_in), .inner_out(outer_out));
    wire [31:0] hierarchical_wire;
    assign hierarchical_wire = inner_inst.inner_reg;
    assign internal_access_out = hierarchical_wire;
endmodule
module DefparamModule (
    input wire d_in,
    output wire d_out
);
    parameter int DELAY = 1;
    wire delayed_wire;
    assign delayed_wire = d_in;
    assign d_out = delayed_wire;
endmodule
module DefparamWrapper (
    input wire wrapper_in,
    input wire [31:0] defparam_val_in,
    output wire wrapper_out,
    output wire [31:0] param_access_out
);
    DefparamModule dp_inst(.d_in(wrapper_in), .d_out(wrapper_out));
    defparam dp_inst.DELAY = defparam_val_in;
    assign param_access_out = dp_inst.DELAY;
endmodule
module PullGateModule (
    input wire pull_in,
    output wire pull_out
);
    wire internal_net;
    pullup(internal_net);
    assign pull_out = internal_net & pull_in;
endmodule
module ConstraintForeachModule (
    input int cf_in [0:3],
    output bit cf_out
);
    class MyClass;
        rand int my_array[0:3];
        constraint array_constr {
            foreach (my_array[k]) {
                my_array[k] > 0;
            }
            foreach (my_array[int idx]) {
                my_array[idx] == cf_in[idx] + 1;
            }
        }
        function new(int arr_in[0:3]);
            my_array = arr_in;
        endfunction
    endclass
    MyClass my_obj;
    always @* begin
        if (my_obj == null) begin
            my_obj = new(cf_in);
        end
        if (my_obj != null) begin
            cf_out = my_obj.randomize();
        end else begin
            cf_out = 1'b0;
        end
    end
endmodule
module ArraySelectModule (
    input wire [7:0] as_in,
    output wire [15:0] as_out,
    output wire [15:0] as_out2,
    output wire [7:0] as_out3
);
    wire [31:0] wide_wire = {as_in, as_in, as_in, as_in};
    assign as_out = wide_wire[15+:16];
    assign as_out2 = wide_wire[31-:16];
    assign as_out3 = wide_wire[23:16];
endmodule
module SimpleInstantiationModule (
    input wire [7:0] sim_in,
    input wire sim_valid,
    output wire [7:0] sim_out,
    output wire sim_out_valid
);
    BasicModule basic_inst (
        .in_data(sim_in),
        .in_valid(sim_valid),
        .out_data(sim_out),
        .out_valid(sim_out_valid)
    );
endmodule
module BoundModule (
    input wire bind_in,
    input wire [0:0] target_signal,
    output wire bind_out
);
    assign bind_out = bind_in & target_signal;
endmodule
module BindTargetModule (
    input wire target_in,
    output wire target_out,
    output wire [0:0] signal_to_bind_to
);
    reg [0:0] internal_signal;
    assign signal_to_bind_to = internal_signal;
    always @* begin
        internal_signal = target_in;
    end
    assign target_out = internal_signal;
endmodule
module BindWrapper (
    input wire wrapper_in,
    input wire bind_in_wrapper,
    output wire wrapper_out,
    output wire bind_access_out
);
    BindTargetModule target_inst (.target_in(wrapper_in), .target_out(wrapper_out));
    bind BindTargetModule target_inst : bound_inst with BoundModule (.bind_in(bind_in_wrapper), .target_signal(target_inst.signal_to_bind_to), .bind_out(bind_access_out));
endmodule
module ArrayInstantiationModule (
    input wire [3:0] array_in,
    output wire [3:0] array_out,
    output wire [7:0] sum_data_out
);
    wire [7:0] data_outs [0:3];
    genvar i;
    for (i = 0; i < 4; i = i + 1) begin : inner_inst_gen
        BasicModule inner_inst (
            .in_data({4'b0, array_in[i], 3'b0}),
            .in_valid(1'b1),
            .out_data(data_outs[i]),
            .out_valid(array_out[i])
        );
    end
    assign sum_data_out = data_outs[0] + data_outs[1] + data_outs[2] + data_outs[3];
endmodule
module GatePrimitiveModule (
    input wire in1,
    input wire in2,
    output wire out
);
    and g1 (out, in1, in2);
endmodule

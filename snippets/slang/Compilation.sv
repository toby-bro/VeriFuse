module data_types_params #(
    parameter int  P_INT  = 10,
    parameter type P_TYPE = logic
)(
    input  logic        i_clk,
    input  logic [7:0]  i_data,
    output logic [15:0] o_result
);
    typedef enum { STATE_IDLE, STATE_RUNNING } state_e;
    typedef struct packed {
        logic [3:0] header;
        logic [1:0] type_field;
    } packet_s;
    localparam int LOCAL_WIDTH = P_INT + 5;
    logic [LOCAL_WIDTH-1:0] internal_reg;
    P_TYPE  type_param_reg;
    packet_s packet_data;
    logic [7:0] unpacked_array [0:3];
    state_e current_state, next_state;
    always_comb begin
        internal_reg    = LOCAL_WIDTH'(i_data) + P_INT;
        type_param_reg  = 1;
        packet_data     = '{header: i_data[7:4], type_field: i_data[3:2]};
        for (int i = 0; i < 4; i++) unpacked_array[i] = i_data + i;
        next_state      = (current_state == STATE_IDLE) ? STATE_RUNNING : STATE_IDLE;
        o_result        = internal_reg;
    end
    always_ff @(posedge i_clk) current_state <= next_state;
endmodule
module nets_alias_clocking(
    input  wire  i_wire_data,
    input  logic i_reg_data,
    input  logic i_clk,
    input  logic i_data_sync,
    output wire  o_wire_out,
    output logic o_reg_out
);
    wire  w_internal;
    logic r_internal;
    assign w_internal  = i_wire_data & i_reg_data;
    assign o_wire_out  = w_internal;
    always_ff @(posedge i_clk) r_internal <= i_data_sync;
    assign o_reg_out = r_internal;
endmodule
module hierarchical_inst(
    input  logic        i_clk,
    input  logic [7:0]  i_data,
    output logic [15:0] o_result
);
    data_types_params #(
        .P_INT (20),
        .P_TYPE(bit)
    ) instance_dtp(
        .i_clk   (i_clk),
        .i_data  (i_data),
        .o_result(o_result)
    );
endmodule
module target_module_for_bind(
    input  logic       i_target_clk,
    input  logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule
module module_to_bind(
    input  logic       i_bind_clk,
    input  logic [3:0] i_bind_control,
    output logic       o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule
module bind_directive_top(
    input  logic       i_clk,
    input  logic [7:0] i_data,
    input  logic [3:0] i_control,
    output logic [7:0] o_result,
    output logic       o_status
);
    target_module_for_bind target_inst(
        .i_target_clk   (i_clk),
        .i_target_data  (i_data),
        .o_target_result(o_result)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (i_clk),
        .i_bind_control (i_control),
        .o_bind_status  (o_status)
    );
endmodule
module defparam_top(
    input  logic        i_clk,
    input  logic [7:0]  i_data,
    output logic [15:0] o_result
);
    hierarchical_inst hi_inst(
        .i_clk   (i_clk),
        .i_data  (i_data),
        .o_result(o_result)
    );
    defparam hi_inst.instance_dtp.P_INT = 50;
endmodule
interface my_interface(input logic clk);
    logic data;
    function int process_data(int value);
        process_data = value + 1;
    endfunction
    modport mp (input data);
endinterface
module interface_extern_dpi(
    input  logic        i_clk,
    input  logic [31:0] i_input_value,
    output logic [31:0] o_processed_value
);
    my_interface iface_inst(.clk(i_clk));
    import "DPI-C" function int dpi_multiply(int a, int b);
    export "DPI-C" task dpi_process_value;
    task dpi_process_value(input int val_in, output int val_out);
        val_out = iface_inst.process_data(val_in);
    endtask
    always_comb begin
        logic [31:0] temp_result;
        temp_result       = logic'(dpi_multiply(i_input_value, 3));
        temp_result       = temp_result + iface_inst.process_data(i_input_value);
        o_processed_value = temp_result;
    end
endmodule
module configuration_top(
    input  logic i_in,
    output logic o_out
);
    assign o_out = i_in;
endmodule
module attributes_test(
    input  logic i_attr_in,
    output logic o_attr_out
);
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = i_attr_in ? 1'b1 : 1'b0;
        o_attr_out      = internal_signal;
    end
endmodule
module simple_adder(
    input  logic a,
    input  logic b,
    output logic sum
);
    assign sum = a + b;
endmodule
module attributes_on_expr_port(
    input  logic i_in,
    input  logic i_control,
    output logic o_out
);
    logic internal_sig;
    assign internal_sig = i_in & i_control;
    simple_adder sa_inst(
        .a  (i_in),
        (* fanout_limit = 10 *) .b(i_control),
        .sum(o_out)
    );
endmodule
class my_class;
    int value;
    function new(int v);
        value = v;
    endfunction
    extern virtual function int get_value();
endclass
function int my_class::get_value();
    return value;
endfunction
module class_outofblock_test(
    input  logic        i_input,
    output logic [31:0] o_output
);
    my_class instance_my_class;
    always_comb begin
        instance_my_class = new(i_input ? 10 : 20);
        o_output = instance_my_class.get_value();
    end
endmodule
module primitive_example(
    input  logic i_p1,
    input  logic i_p2,
    output logic o_p_and,
    output logic o_p_xor
);
    and (o_p_and, i_p1, i_p2);
    xor (o_p_xor, i_p1, i_p2);
endmodule
module extern_declarations(
    input  logic i_in,
    output logic o_out
);
    assign o_out = i_in;
endmodule
module assertion_example(
    input  logic i_clk,
    input  logic i_enable,
    input  logic i_data,
    output logic o_dummy
);
    property p_data_stable_when_enabled;
        @(posedge i_clk) i_enable |-> $stable(i_data);
    endproperty
    assert property (p_data_stable_when_enabled);
    assign o_dummy = i_data;
endmodule
module name_conflict_example(
    input  logic i_in,
    output logic o_out
);
    parameter int my_param = 5;
    logic my_var;
    always_comb my_var = i_in;
    assign o_out = i_in && (my_param == 5) && my_var;
endmodule
module unreferenced_module(
    input  logic unused_in,
    output logic unused_out
);
    assign unused_out = ~unused_in;
endmodule

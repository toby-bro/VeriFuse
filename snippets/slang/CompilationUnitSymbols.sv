timeunit 1ns;
timeprecision 1ps;
`default_nettype none
module cu_timeunit_mod (
    input logic clk,
    output logic reset
);
    logic internal_sig;
    always_ff @(posedge clk) begin
        reset <= 1'b0;
        internal_sig = clk;
    end
endmodule
module cu_base (
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    assign data_out = data_in;
endmodule
package pkg_data;
    typedef enum { IDLE, READ, WRITE } state_e;
    parameter int DATA_WIDTH = 16;
    localparam int ADDR_WIDTH = 8;
    typedef struct packed {
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] data;
    } data_struct_t;
    function automatic int add_one(input int val);
        return val + 1;
    endfunction
endpackage
import pkg_data::*;
package pkg_import_export;
    export pkg_data::state_e;
    export pkg_data::DATA_WIDTH;
    export pkg_data::add_one;
    parameter int EXPORT_PARAM = add_one(pkg_data::ADDR_WIDTH);
endpackage
module def_params_ansi #(
    parameter int P_INT_DEF = 32,
    parameter type P_TYPE_DEF = logic,
    localparam string LP_STRING = "hello",
    localparam int LP_CALC = P_INT_DEF * 2,
    parameter int P_NO_DEF,
    parameter type P_TYPE_NO_DEF
) (
    input P_TYPE_DEF data_in_port_type,
    output P_TYPE_DEF data_out_port_type,
    input logic [P_INT_DEF-1:0] data_in_port_val,
    output logic [P_INT_DEF-1:0] data_out_port_val,
    input logic dummy_in,
    output logic dummy_out
);
    parameter int BODY_P_INT = P_INT_DEF + 1;
    localparam type BODY_LP_TYPE = logic [LP_CALC-1:0];
    localparam int BODY_LP_NO_INIT = 1;
    parameter int BODY_P_NO_INIT = 2;
    BODY_LP_TYPE internal_data;
    state_e current_state;
    always_comb begin
        data_out_port_type = data_in_port_type;
        data_out_port_val = data_in_port_val;
        dummy_out = dummy_in;
        internal_data = '0;
        current_state = IDLE;
    end
    always @(*) begin
        logic procedural_var;
        procedural_var = dummy_in;
    end
endmodule
module def_nonansi_params (
    data_in_nonansi,
    data_out_nonansi,
    control_in,
    control_out
);
    parameter int VAL_PARAM = 10;
    localparam type TYPE_PARAM = int;
    input [VAL_PARAM-1:0] data_in_nonansi;
    output logic [VAL_PARAM-1:0] data_out_nonansi;
    input logic control_in;
    output logic control_out;
    TYPE_PARAM internal_val;
    always_comb begin
        data_out_nonansi = data_in_nonansi;
        control_out = control_in;
        internal_val = VAL_PARAM;
    end
endmodule
module def_lifetime (
    input logic clk,
    output logic state_out
);
    static logic initialized_reg = 1'b1;
    always_ff @(posedge clk) begin
        automatic logic [3:0] counter;
        counter = counter + 1;
        state_out <= initialized_reg & counter[0];
    end
endmodule
interface intf_basic #(parameter WIDTH = 8)();
    logic [WIDTH-1:0] bus_data;
    logic bus_valid;
    modport controller (
        output bus_data,
        output bus_valid
    );
    modport peripheral (
        input bus_data,
        input bus_valid
    );
endinterface
program prg_basic (input logic start, output logic done);
    logic internal_flag;
    initial begin
        internal_flag = start;
        done = internal_flag;
    end
endprogram
module top_module_config_dummy (input logic i, output logic o); assign o = i; endmodule
module child_module_v1_config_dummy (input logic i, output logic o); assign o = ~i; endmodule
module child_module_v2_config_dummy (input logic i, output logic o); assign o = i | i; endmodule
module another_module_config_dummy (input logic i, output logic o); assign o = i & i; endmodule
module module_using_package_typedef (
    input pkg_data::data_struct_t input_struct,
    output pkg_data::data_struct_t output_struct
);
    assign output_struct = input_struct;
endmodule
module module_using_package_param (
    input logic [pkg_data::DATA_WIDTH-1:0] wide_data_in,
    output logic [pkg_data::DATA_WIDTH-1:0] wide_data_out
);
    assign wide_data_out = wide_data_in;
endmodule
module module_with_unconnected_drive (
    input logic in_data,
    output logic out_data_pull1,
    output logic out_data_pull0
);
    assign out_data_pull1 = in_data;
    assign out_data_pull0 = ~in_data;
endmodule

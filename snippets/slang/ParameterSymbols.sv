class base_packet;
    int header;
endclass
class derived_packet extends base_packet;
    int payload;
endclass
module param_types #(
    parameter integer P_INT = 10,
    parameter logic [7:0] P_LOGIC = 8'hAA,
    parameter real P_REAL = 2.718,
    parameter string P_STRING = "verilog"
)(
    input logic i_clk,
    output logic [15:0] o_data
);
    parameter bit [3:0][2:0] P_PACKED_ARRAY = '{ '{1,2,3}, '{4,5,6}, '{7,8,9}, '{10,11,12} };
    parameter integer UNPACKED_ARR_SIZE = 2;
    parameter integer P_UNPACKED_ARRAY [UNPACKED_ARR_SIZE] = '{50, 75};
    always_comb begin
        o_data = P_INT + P_PACKED_ARRAY[0][0] + P_UNPACKED_ARRAY[1] + $size(P_STRING);
    end
endmodule
module param_local_port #(
    parameter int P_PORT_VAL = 25
)(
    input logic i_reset,
    output logic [7:0] o_sum
);
    localparam int LP_BODY_VAL = 125;
    localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
    always_comb begin
        if (i_reset) begin
            o_sum = 0;
        end else begin
            o_sum = LP_CALCULATED;
        end
    end
endmodule
module param_defaults #(
    parameter int BASE_OFFSET = 7,
    parameter int SCALE_FACTOR = 3,
    parameter int DERIVED_VALUE = (BASE_OFFSET + 10) * SCALE_FACTOR
)(
    input logic [1:0] i_select,
    output int o_selected_val
);
    parameter int OptionValues [3] = '{BASE_OFFSET, SCALE_FACTOR, DERIVED_VALUE};
    always_comb begin
        case (i_select)
            0: o_selected_val = OptionValues[0];
            1: o_selected_val = OptionValues[1];
            2: o_selected_val = OptionValues[2];
            default: o_selected_val = 0;
        endcase
    end
endmodule
module param_implicit_string (
    input logic [1:0] i_char_index,
    output logic [7:0] o_ascii_char
);
    parameter IMPLICIT_STR = "System";
    parameter string EXPLICIT_STR = "Verilog";
    always_comb begin
        if (i_char_index < $size(IMPLICIT_STR)) begin
            o_ascii_char = IMPLICIT_STR[i_char_index];
        end else begin
             o_ascii_char = EXPLICIT_STR[0];
        end
    end
endmodule
module type_param_basic #(
    parameter type T_PORT_TYPE = int,
    parameter type T_ANOTHER_PORT_TYPE = bit
)(
    input T_PORT_TYPE i_data,
    output T_ANOTHER_PORT_TYPE o_data,
    output integer o_body_type_bits
);
    parameter type T_BODY_TYPE = logic [63:0];
    T_BODY_TYPE internal_reg;
    always_comb begin
        internal_reg = 64'hFEDC_BA98_7654_3210;
        o_data = T_ANOTHER_PORT_TYPE'(i_data);
    end
    assign o_body_type_bits = $bits(T_BODY_TYPE);
endmodule
module type_param_restricted #(
    parameter type T_CLASS_OK,
    parameter type T_CLASS_ERROR
)(
    input logic i_enable,
    output logic o_status
);
    always_comb begin
        o_status = i_enable;
    end
endmodule
module defparam_basic #(
    parameter int P_MOD_PARAM = 500
)(
    input logic i_valid,
    output int o_param_value
);
    defparam P_MOD_PARAM = 750;
    always_comb begin
        o_param_value = P_MOD_PARAM;
    end
endmodule
module defparam_errors #(
    parameter int P_VALID_TARGET = 1000
)(
    input logic i_trigger,
    output int o_valid_param
);
    logic internal_signal;
    defparam P_VALID_TARGET = 1100;
    always_comb begin
        o_valid_param = P_VALID_TARGET;
        internal_signal = i_trigger;
    end
endmodule
module specparam_basic (
    input wire i_data_in,
    output logic o_data_out 
);
    specify
        specparam basic_delay = 5;
        (i_data_in => o_data_out) = basic_delay;
    endspecify
    always_comb begin
        o_data_out = i_data_in;
    end
endmodule
module specparam_pathpulse (
    input wire i_input_a,
    input wire i_input_b,
    output logic o_output_x, 
    output logic o_output_y 
);
    specify
        specparam PATHPULSE$i_input_a$o_output_x = (1ps, 2ps);
        specparam PATHPULSE$i_input_b$o_output_y = (3ps, 4ps);
        (i_input_a => o_output_x) = (10ps, 10ps);
        (i_input_b => o_output_y) = (12ps, 12ps);
    endspecify
    always_comb begin
        o_output_x = i_input_a;
        o_output_y = i_input_b;
    end
endmodule
module specparam_pathpulse_errors (
    input wire i_term_in,
    output logic o_term_out 
);
    logic internal_sig;
    specify
        (i_term_in => o_term_out) = (20ps, 20ps);
    endspecify
    always_comb begin
        o_term_out = i_term_in;
        internal_sig = i_term_in | o_term_out;
    end
endmodule

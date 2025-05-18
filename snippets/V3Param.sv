typedef struct packed {
    logic enable;
    int value;
} my_struct;
typedef logic [127:0] my_packed_array;
typedef logic [4:0] my_fwd_type;
typedef logic [9:0] my_fwd_type_param;
typedef logic [15:0] fwd_override_t;
interface iface_params #(
    parameter int IF_W = 8
);
    logic [IF_W-1:0] data;
    logic clk;
    modport mp (input clk, output data);
endinterface
class class_params #(
    parameter int CLS_SZ = 32
);
    logic [CLS_SZ-1:0] data;
    function new(logic [CLS_SZ-1:0] initial_data);
        data = initial_data;
    endfunction
    function logic [CLS_SZ-1:0] get_data();
        return data;
    endfunction
endclass
module mod_value_basic #(
    parameter int WIDTH = 8
) (
    input logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    assign out = in + 1;
endmodule
module mod_value_inst #(
    parameter int SIZE = 16
) (
    input logic [SIZE-1:0] main_in,
    output logic [SIZE-1:0] main_out
);
    mod_value_basic #(.WIDTH(SIZE)) inst_sized (.in(main_in), .out(main_out));
endmodule
module mod_type_basic #(
    parameter type T = logic
) (
    input T in,
    output T out
);
    assign out = in;
endmodule
module mod_type_inst #(
    parameter type DATA_TYPE = int
) (
    input DATA_TYPE main_in,
    output DATA_TYPE main_out
);
    mod_type_basic #(.T(DATA_TYPE)) inst_typed (.in(main_in), .out(main_out));
endmodule
module mod_params_all #(
    parameter int P_INT = 10,
    parameter logic [7:0] P_SIZED = 8'hAA,
    parameter string P_STRING = "default string",
    parameter real P_REAL = 3.14,
    parameter type P_TYPE = logic
) (
    input logic [P_INT-1:0] in_val,
    output P_TYPE out_val
);
    assign out_val = in_val;
endmodule
module mod_inst_all #(
    parameter int OVERRIDE_SIZE = 20,
    parameter type OVERRIDE_TYPE = bit [19:0]
) (
    input logic [OVERRIDE_SIZE-1:0] main_in,
    output logic [10-1:0] main_out_default,
    output logic [OVERRIDE_SIZE-1:0] main_out_sized,
    output byte main_out_byte,
    output OVERRIDE_TYPE main_out_typed
);
    localparam DEFAULT_P_INT = 10;
    logic [DEFAULT_P_INT-1:0] inst_default_out;
    OVERRIDE_TYPE inst_override1_out;
    byte inst_override3_out;
    logic dummy_out;
    mod_params_all inst_default (
        .in_val({DEFAULT_P_INT{1'b0}}),
        .out_val(inst_default_out)
    );
    mod_params_all #(.P_INT(OVERRIDE_SIZE), .P_TYPE(OVERRIDE_TYPE)) inst_override1 (
        .in_val(main_in),
        .out_val(inst_override1_out)
    );
    mod_params_all #(.P_SIZED(8'h55), .P_STRING("override string")) inst_override2 (
        .in_val({DEFAULT_P_INT{1'b0}}),
        .out_val(dummy_out)
    );
    mod_params_all #(.P_REAL(2.718), .P_INT(8), .P_TYPE(byte)) inst_override3 (
        .in_val({8{1'b0}}),
        .out_val(inst_override3_out)
    );
    assign main_out_default = inst_default_out;
    assign main_out_sized = inst_override1_out;
    assign main_out_byte = inst_override3_out;
    assign main_out_typed = inst_override1_out;
endmodule
module mod_leaf (
    input logic in_leaf,
    output logic out_leaf
);
    assign out_leaf = ~in_leaf;
endmodule
module mod_gen_all #(
    parameter int G_SELECT = 1,
    parameter int G_COUNT = 2
) (
    input logic gen_in,
    output logic gen_out
);
    logic temp_out_if;
    logic [G_COUNT-1:0] temp_out_for;
    logic temp_out_case;
    assign gen_out = temp_out_if | (|temp_out_for) | temp_out_case;
    generate
        if (G_SELECT == 1) begin : gen_if_block
            mod_leaf leaf_if (.in_leaf(gen_in), .out_leaf(temp_out_if));
        end else begin : gen_if_else_block
            assign temp_out_if = gen_in;
        end
    endgenerate
    generate
        case (G_SELECT)
            1: begin : gen_case_1
                assign temp_out_case = gen_in;
            end
            2: begin : gen_case_2
                mod_leaf leaf_case (.in_leaf(gen_in), .out_leaf(temp_out_case));
            end
            default: begin : gen_case_default
                assign temp_out_case = ~gen_in;
            end
        endcase
    endgenerate
    generate
        for (genvar i = 0; i < G_COUNT; i++) begin : gen_for_block
            mod_leaf leaf_for (.in_leaf(gen_in), .out_leaf(temp_out_for[i]));
        end
    endgenerate
endmodule
interface iface_params_inst # (parameter int I_W = 8) ();
    logic [I_W-1:0] data_p;
    modport mp_in (input data_p);
    modport mp_out (output data_p);
endinterface
module mod_uses_iface_params #(
    parameter int MOD_IF_W = 16
) (
    iface_params if_port,
    input logic dummy_in,
    output logic [MOD_IF_W-1:0] if_data_out
);
    always @(posedge if_port.clk) begin
        if_port.data <= {MOD_IF_W{dummy_in}};
    end
    assign if_data_out = if_port.data;
endmodule
module mod_iface_inst (
    input logic main_dummy_in,
    input logic main_clk,
    input logic main_rst_n,
    output logic [15:0] main_if_data_out,
    output logic [63:0] main_class_out_data
);
    iface_params #(.IF_W(16)) if_inst ();
    assign if_inst.clk = main_clk;
    mod_uses_iface_params #(.MOD_IF_W(16)) mod_inst (
        .if_port(if_inst),
        .dummy_in(main_dummy_in),
        .if_data_out(main_if_data_out)
    );
    mod_uses_class_params #(.MOD_CLS_SZ(64)) class_mod_inst (
        .class_in_data({64{main_dummy_in}}),
        .clk(main_clk),
        .rst_n(main_rst_n),
        .class_out_data(main_class_out_data)
    );
endmodule
module mod_uses_class_params #(
    parameter int MOD_CLS_SZ = 64
) (
    input logic [MOD_CLS_SZ-1:0] class_in_data,
    input bit clk,
    input bit rst_n,
    output logic [MOD_CLS_SZ-1:0] class_out_data
);
    class_params #(.CLS_SZ(MOD_CLS_SZ)) cls_h;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cls_h = null;
        end else begin
            if (cls_h == null) begin
                cls_h = new(class_in_data);
            end
        end
    end
    assign class_out_data = (cls_h != null) ? cls_h.get_data() : {MOD_CLS_SZ{1'b0}};
endmodule
module mod_array_param #(
    parameter logic [7:0] ARRAY_P [4] = '{8'h11, 8'h22, 8'h33, 8'h44}
) (
    input int index,
    output logic [($bits(ARRAY_P[0]) * $size(ARRAY_P)) - 1 : 0] val_flat,
    output logic [$bits(ARRAY_P[0])-1 : 0] val_element
);
    localparam ELEM_WIDTH = $bits(ARRAY_P[0]);
    localparam ARRAY_SIZE = $size(ARRAY_P);
    logic [ELEM_WIDTH-1:0] temp_array [ARRAY_SIZE];
    assign temp_array = ARRAY_P;
    genvar i_concat;
    generate
        for(i_concat = 0; i_concat < ARRAY_SIZE; i_concat++) begin : concat_gen
            assign val_flat[((ARRAY_SIZE - 1 - i_concat) * ELEM_WIDTH) +: ELEM_WIDTH] = temp_array[i_concat];
        end
    endgenerate
    assign val_element = (index >= 0 && index < ARRAY_SIZE) ? temp_array[index] : 'x;
endmodule
module mod_array_param_inst (
    input int inst_index,
    output logic [($bits(8'h0) * 4) - 1 : 0] inst_val_flat,
    output logic [$bits(8'h0)-1 : 0] inst_val_element
);
    mod_array_param inst_def (.index(inst_index), .val_flat(inst_val_flat), .val_element(inst_val_element));
endmodule
module mod_type_params_complex #(
    parameter type C_STRUCT_TYPE = my_struct,
    parameter type C_PACKED_TYPE = my_packed_array
) (
    input C_STRUCT_TYPE in_struct,
    output C_PACKED_TYPE out_packed
);
    localparam INT_WIDTH = $bits(in_struct.value);
    localparam PACKED_WIDTH = $bits(out_packed);
    generate
        if (PACKED_WIDTH == 0 || INT_WIDTH == 0 || (PACKED_WIDTH % INT_WIDTH) != 0) begin : size_mismatch_error
            assign out_packed = 'x;
        end else begin : size_match_assign
            localparam REPEAT_COUNT = PACKED_WIDTH / INT_WIDTH;
            assign out_packed = {REPEAT_COUNT {in_struct.value}};
        end
    endgenerate
endmodule
module mod_type_params_complex_inst (
    input my_struct inst_in_struct,
    output my_packed_array inst_out_packed
);
    mod_type_params_complex inst_def (.in_struct(inst_in_struct), .out_packed(inst_out_packed));
endmodule
module mod_recursive (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule
module mod_hier_block #(
    parameter int H_WIDTH = 16
) (
    input logic [H_WIDTH-1:0] in,
    output logic [H_WIDTH-1:0] out
);
    assign out = in + 1;
endmodule
module mod_hier_inst (
    input logic [31:0] in_32,
    output logic [31:0] out_32,
    input logic [7:0] in_8,
    output logic [7:0] out_8
);
    mod_hier_block #(.H_WIDTH(32)) inst_32 (.in(in_32), .out(out_32));
    mod_hier_block #(.H_WIDTH(8)) inst_8 (.in(in_8), .out(out_8));
endmodule
module mod_uses_fwd_typedef (
    input my_fwd_type in_val,
    output my_fwd_type out_val
);
    assign out_val = in_val;
endmodule
module mod_param_fwd_typedef #(
    parameter type FWD_T = my_fwd_type_param
) (
    input FWD_T in,
    output FWD_T out
);
    assign out = in;
endmodule
module mod_param_type_fwd_typedef #(
    parameter type T = logic
) (
    input T in,
    output T out
);
    assign out = in;
endmodule
module mod_param_type_fwd_typedef_inst (
    input fwd_override_t in_val,
    output fwd_override_t out_val
);
    mod_param_type_fwd_typedef #(.T(fwd_override_t)) inst (.in(in_val), .out(out_val));
endmodule

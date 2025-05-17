module module_a #(parameter WIDTH = 8) (
    input logic [WIDTH-1:0] in_a,
    input logic [WIDTH-1:0] in_b,
    output logic [WIDTH-1:0] out_sum,
    output logic [WIDTH-1:0] out_diff
);
    logic [WIDTH-1:0] sum_internal;
    logic [WIDTH-1:0] diff_internal;
    always_comb begin
        sum_internal = in_a + in_b;
        diff_internal = in_a - in_b;
    end
    assign out_sum = sum_internal;
    assign out_diff = diff_internal;
endmodule
module module_b (
    input logic [7:0] in_data1,
    input logic [7:0] in_data2,
    output logic [7:0] sum_result,
    output logic [7:0] diff_result
);
    module_a #( .WIDTH(8) ) inst_named (
        .in_a   (in_data1),
        .in_b   (in_data2),
        .out_sum(sum_result),
        .out_diff(diff_result)
    );
endmodule
module module_c (
    input logic [15:0] data1,
    input logic [15:0] data2,
    output logic [15:0] sum_out,
    output logic [15:0] diff_out
);
    module_a #(16) inst_positional (
        data1,
        data2,
        sum_out,
        diff_out
    );
endmodule
module module_d (
    input logic [3:0] in_a_d,
    input logic [3:0] in_b_d,
    output logic [3:0] out_sum_d,
    output logic [3:0] out_diff_d
);
    module_a #(4) inst_dot_star ( .* );
endmodule
module module_para #(parameter DATA_WIDTH = 32) (
    input logic [DATA_WIDTH-1:0] in_val,
    output logic [DATA_WIDTH-1:0] out_val
);
    assign out_val = in_val;
endmodule
module module_e (
    input logic [63:0] input_data,
    input logic dummy_in_e,
    output logic [63:0] output_data,
    output logic dummy_out_e
);
    module_para #( .DATA_WIDTH(64) ) inst_param (
        .in_val(input_data),
        .out_val(output_data)
    );
    assign dummy_out_e = dummy_in_e;
endmodule
module module_f (
    input logic [7:0] input1,
    input logic dummy_in_f,
    output logic [7:0] output1,
    output logic dummy_out_f
);
    module_a #(8) inst_missing (
        .in_a   (input1),
        .in_b   (),
        .out_sum(output1)
    );
    assign dummy_out_f = dummy_in_f;
endmodule
module recursive_module (
    input logic [0:0] enable_in,
    input logic dummy_rec_in,
    output logic [0:0] out_rec,
    output logic dummy_rec_out
);
    wire [0:0] internal_enable;
    assign out_rec = enable_in;
    recursive_module recursive_instance (
        .enable_in(internal_enable),
        .dummy_rec_in(dummy_rec_in),
        .out_rec(),
        .dummy_rec_out()
    );
    assign internal_enable = enable_in;
    assign dummy_rec_out = dummy_rec_in;
endmodule
interface my_interface (input logic clk);
    logic [7:0] data;
    logic       valid;
    logic       ready;
    modport producer (output data, valid, input ready);
    modport consumer (input data, valid, output ready);
endinterface
module module_g (
    input logic system_clk,
    my_interface.producer producer_if,
    my_interface.consumer consumer_if,
    input logic dummy_in_g,
    output logic dummy_out_g
);
    my_interface if_instance (system_clk);
    logic [7:0] processed_data;
    assign processed_data = consumer_if.data;
    assign producer_if.data = processed_data;
    assign if_instance.data = producer_if.data;
    assign producer_if.valid = if_instance.valid;
    assign if_instance.valid = producer_if.valid;
    assign consumer_if.ready = if_instance.ready;
    assign if_instance.ready = consumer_if.ready;
    assign dummy_out_g = dummy_in_g;
endmodule
package my_package;
    const logic [7:0] MY_CONSTANT = 8'hAA;
    function automatic logic [7:0] add_one(logic [7:0] val);
        return val + 1;
    endfunction
    typedef enum { STATE_IDLE, STATE_BUSY } my_enum_t;
    typedef struct {
        int id;
        logic [7:0] data;
    } pkg_struct_t;
endpackage
module module_h (
    input logic [7:0] pkg_in,
    input logic another_in_h,
    output logic [7:0] pkg_out,
    output logic another_out_h
);
    import my_package::*;
    logic [7:0] temp;
    assign temp = add_one(pkg_in) + MY_CONSTANT;
    assign pkg_out = temp;
    assign another_out_h = another_in_h;
endmodule
module bind_target (
    input logic bt_in,
    output logic bt_out
);
    assign bt_out = bt_in;
endmodule
module inverter (
    input logic inv_in,
    output logic inv_out
);
    assign inv_out = ~inv_in;
endmodule
module module_i (
    input logic bind_test_in,
    input logic dummy_bind_in_i,
    output logic bind_test_out,
    output logic dummy_bind_out_i
);
    wire unconnected_inv_out_inv_cell;
    bind_target bt_inst (.bt_in(bind_test_in), .bt_out(bind_test_out));
    bind bind_target : bt_inst begin
        inverter inv_cell (.inv_in(bt_inst.bt_out), .inv_out(unconnected_inv_out_inv_cell));
    endbind
    assign dummy_bind_out_i = dummy_bind_in_i;
endmodule
module module_j (
    input logic [7:0] attr_in,
    input logic dummy_in_j,
    output logic [7:0] attr_out,
    output logic dummy_out_j
);
    (* full_case, parallel_case *)
    reg [7:0] attributed_reg;
    always_comb begin
        case(attr_in)
            8'h00: attributed_reg = 8'hFF;
            default: attributed_reg = attr_in;
        endcase
    end
    assign attr_out = attributed_reg;
    assign dummy_out_j = dummy_in_j;
endmodule
module module_k (
    input logic [7:0] in_data_array [0:2],
    input logic dummy_in_k,
    output logic [7:0] out_sum_array [0:2],
    output logic dummy_out_k
);
    genvar i;
    generate
        for (i = 0; i < 3; i = i + 1) begin : inst_array_gen
            module_a #(8) inst_single (
                .in_a   (in_data_array[i]),
                .in_b   (in_data_array[i]),
                .out_sum(out_sum_array[i]),
                .out_diff()
            );
        end
    endgenerate
    assign dummy_out_k = dummy_in_k;
endmodule
class my_class;
    int value = 0;
    function new(int initial_value);
        value = initial_value;
    endfunction
    function int get_value();
        return value;
    endfunction
endclass
module module_l (
    input int initial_val_in,
    input logic dummy_in_l,
    output int class_value_out,
    output logic dummy_out_l
);
    my_class my_inst_handle;
    always_comb begin
        if (my_inst_handle == null) begin
          my_inst_handle = new(initial_val_in);
        end else begin
          my_inst_handle.value = initial_val_in;
        end
    end
    assign class_value_out = (my_inst_handle != null) ? my_inst_handle.get_value() : 0;
    assign dummy_out_l = dummy_in_l;
endmodule
module module_m (
    input logic [7:0] in_m,
    input logic dummy_in_m,
    output logic [7:0] out_m_diff,
    output logic dummy_out_m
);
    module_a #(8) inst_empty_port (
        .in_a   (in_m),
        .in_b   (8'h0),
        .out_sum(),
        .out_diff(out_m_diff)
    );
    assign dummy_out_m = dummy_in_m;
endmodule
interface my_interface_param #(parameter DATA_WIDTH=8);
    logic [DATA_WIDTH-1:0] data;
    logic valid;
    modport mp (output data, valid);
endinterface
module module_n (
    input logic dummy_in_n,
    input logic extra_in_n,
    output logic dummy_out_n,
    output logic extra_out_n
);
    my_interface_param #(16) param_if_inst;
    logic [15:0] temp_data;
    assign temp_data = param_if_inst.data;
    assign param_if_inst.data = {16{dummy_in_n}};
    assign param_if_inst.valid = extra_in_n;
    assign dummy_out_n = param_if_inst.valid;
    assign extra_out_n = temp_data[0];
endmodule
interface my_interface_array #(parameter NUM_CH = 2);
    logic [7:0] data [NUM_CH-1:0];
endinterface
module module_o (
    input logic dummy_in_o,
    input logic [7:0] array_in_val,
    output logic dummy_out_o,
    output logic [7:0] array_out_val
);
    my_interface_array #(4) if_array_var;
    assign if_array_var.data[0] = array_in_val;
    assign if_array_var.data[1] = 8'h55;
    assign array_out_val = if_array_var.data[0];
    assign dummy_out_o = if_array_var.data[1][0];
endmodule
module module_q (
    input logic [7:0] in_required,
    input logic [7:0] in_optional = 8'hFF,
    output logic [7:0] out_sum_q,
    output logic dummy_out_q
);
    assign out_sum_q = in_required + in_optional;
    assign dummy_out_q = out_sum_q[0];
endmodule
module module_p (
    input logic [7:0] data_in_p,
    input logic dummy_in_p,
    output logic [7:0] result_out_p,
    output logic dummy_out_p
);
    module_q inst_q (
        .in_required(data_in_p),
        .out_sum_q(result_out_p),
        .dummy_out_q(dummy_out_p)
    );
endmodule
module module_r (
    input logic r_clk,
    input logic [7:0] r_data_in,
    output logic [7:0] r_data_out,
    output logic r_valid_out
);
    my_interface if_cell_inst (r_clk);
    assign if_cell_inst.data = r_data_in;
    assign if_cell_inst.valid = 1'b1;
    assign if_cell_inst.ready = 1'b1;
    assign r_data_out = if_cell_inst.data;
    assign r_valid_out = if_cell_inst.valid;
endmodule
module module_s (
    input logic [7:0] s_in,
    input logic dummy_in_s,
    output logic [7:0] s_out,
    output logic dummy_out_s
);
    import my_package::add_one;
    import my_package::MY_CONSTANT;
    logic [7:0] temp;
    assign temp = add_one(s_in) + MY_CONSTANT;
    assign s_out = temp;
    assign dummy_out_s = dummy_in_s;
endmodule
module module_t (
    input logic t_clk,
    input logic dummy_in_t,
    my_interface t_if_port,
    output logic dummy_out_t
);
    logic [7:0] received_data;
    assign received_data = t_if_port.data;
    assign t_if_port.valid = 1'b1;
    assign dummy_out_t = received_data[0];
endmodule
typedef struct {
    logic [7:0] field1;
    int         field2;
} my_struct_t;
module module_u (
    input my_struct_t in_struct,
    input logic dummy_in_u,
    output int out_field2,
    output logic dummy_out_u
);
    my_struct_t internal_struct;
    always_comb begin
        internal_struct = in_struct;
    end
    assign out_field2 = internal_struct.field2;
    assign dummy_out_u = dummy_in_u;
endmodule
module module_v (
    input logic dummy_in_v,
    output logic dummy_out_v
);
    export my_package::*;
    assign dummy_out_v = dummy_in_v;
endmodule
module module_w (
    input logic clock_w,
    input logic [7:0] data_in_w,
    output logic [7:0] data_out_w,
    output logic valid_out_w
);
    my_interface actual_if_instance (clock_w);
    wire my_interface if_wire_var = actual_if_instance;
    assign data_out_w = if_wire_var.data;
    assign valid_out_w = if_wire_var.valid;
    assign actual_if_instance.data = data_in_w;
    assign actual_if_instance.valid = 1'b1;
    assign actual_if_instance.ready = 1'b1;
endmodule
module module_x (
    input logic dummy_in_x,
    input my_package::pkg_struct_t in_struct_x,
    output logic dummy_out_x,
    output int out_id_x
);
    typedef my_package::pkg_struct_t local_pkg_struct_t;
    local_pkg_struct_t internal_struct;
    always_comb begin
        internal_struct = in_struct_x;
    end
    assign out_id_x = internal_struct.id;
    assign dummy_out_x = dummy_in_x;
endmodule
module module_y (
    input logic clk_y,
    input logic dummy_in_y,
    output logic [7:0] data_out_y,
    output logic dummy_out_y
);
    my_interface if_array_inst [2] (clk_y);
    assign if_array_inst[0].data = 8'h11;
    assign if_array_inst[0].valid = 1'b1;
    assign if_array_inst[0].ready = 1'b0;
    assign if_array_inst[1].data = 8'h22;
    assign if_array_inst[1].valid = 1'b0;
    assign if_array_inst[1].ready = 1'b1;
    assign data_out_y = if_array_inst[0].data | if_array_inst[1].data;
    assign dummy_out_y = dummy_in_y & if_array_inst[0].valid & ~if_array_inst[1].valid;
endmodule
module module_z (
    input logic [7:0] unpacked_in [0:3],
    input logic dummy_in_z,
    output logic [7:0] unpacked_out [0:3],
    output logic dummy_out_z
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : array_port_gen
            assign unpacked_out[i] = unpacked_in[i] + i;
        end
    endgenerate
    assign dummy_out_z = dummy_in_z;
endmodule
module module_aa (
    input struct packed {
        logic [7:0] field_a;
        int         field_b;
    } packed_struct_in,
    input logic dummy_in_aa,
    output logic [7:0] packed_struct_out_a,
    output int packed_struct_out_b,
    output logic dummy_out_aa
);
    assign packed_struct_out_a = packed_struct_in.field_a;
    assign packed_struct_out_b = packed_struct_in.field_b + 1;
    assign dummy_out_aa = dummy_in_aa;
endmodule
module module_bb (
    input union {
        logic [15:0] u_word;
        logic [7:0]  u_byte [2];
        int          u_int;
    } union_in,
    input logic dummy_in_bb,
    output logic [15:0] union_out_word,
    output logic dummy_out_bb
);
    assign union_out_word = union_in.u_word;
    assign dummy_out_bb = dummy_in_bb;
endmodule

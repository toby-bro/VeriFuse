module SimpleCombinational (
    input wire in1,
    input wire in2,
    output wire out_and
);
    assign out_and = in1 & in2;
endmodule
module BasicSequential (
    input wire clk,
    input wire d_in,
    output reg q_out
);
    always_ff @(posedge clk) begin
        q_out <= d_in;
    end
endmodule
module MuxCase (
    input wire [1:0] sel,
    input wire [7:0] data_a,
    input wire [7:0] data_b,
    input wire [7:0] data_c,
    output reg [7:0] data_out
);
    always_comb begin
        case (sel)
            2'b00: data_out = data_a;
            2'b01: data_out = data_b;
            2'b10: data_out = data_c;
            default: data_out = 8'hFF;
        endcase
    end
endmodule
module HierChild (
    input wire child_enable,
    input wire [15:0] child_data_in,
    output wire [15:0] child_data_out
);
    assign child_data_out = child_enable ? child_data_in : 16'b0;
endmodule
module ComplexCombinational (
    input wire condition,
    input wire [7:0] data_a,
    input wire [7:0] data_b,
    input wire [2:0] index,
    input wire [7:0] data_array [0:7],
    output reg [7:0] result_vec,
    output wire result_scalar
);
    always_comb begin
        if (condition) begin
            result_vec = data_a | data_array[index];
        end else begin
            result_vec = data_b & data_array[index];
        end
    end
    assign result_scalar = |result_vec;
endmodule
module IntegerModule (
    input integer int_in1,
    input integer int_in2,
    input wire scalar_in,
    output integer int_out
);
    always_comb begin
        if (scalar_in) begin
            int_out = int_in1 + int_in2;
        end else begin
            int_out = int_in1 - int_in2;
        end
    end
endmodule
module MemoryModule (
    input wire clk,
    input wire write_en,
    input wire [3:0] addr,
    input wire [7:0] write_data,
    output wire [7:0] read_data
);
    reg [7:0] mem [0:15];
    always_ff @(posedge clk) begin
        if (write_en) begin
            mem[addr] <= write_data;
        }
    end
    assign read_data = mem[addr];
endmodule
module LoopModule #(parameter WIDTH = 8) (
    input wire [WIDTH-1:0] data_in,
    input wire enable,
    output reg [WIDTH-1:0] data_out
);
    always_comb begin
        if (enable) begin
            for (int i = 0; i < WIDTH; i = i + 1) begin
                if (i < WIDTH) data_out[i] = data_in[WIDTH - 1 - i];
            end
        end else begin
            data_out = data_in;
        end
    end
endmodule
module ParameterizedModule #(parameter DATA_WIDTH = 16, parameter SHIFT_MAX = 4) (
    input wire [DATA_WIDTH-1:0] input_val,
    input wire [($clog2(SHIFT_MAX == 0 ? 1 : SHIFT_MAX)) - 1 : 0] shift_amount_in,
    output wire [DATA_WIDTH-1:0] output_val
);
    localparam int ACTUAL_SHIFT_MAX = (SHIFT_MAX == 0) ? 1 : SHIFT_MAX;
    localparam int SHIFT_BITS = $clog2(ACTUAL_SHIFT_MAX);
    localparam int MAX_SHIFT_VAL = (DATA_WIDTH > 0) ? DATA_WIDTH - 1 : 0;
    localparam int SHIFT_OP_WIDTH = (MAX_SHIFT_VAL == 0 && DATA_WIDTH > 0) ? 1 :
                                    (DATA_WIDTH == 0) ? 0 :
                                    $clog2(MAX_SHIFT_VAL + 1);
    logic [31:0] shift_amount_extended_int;
    int safe_shift_amount_int;
    logic [SHIFT_OP_WIDTH-1:0] final_shift_amount;
    assign shift_amount_extended_int = (SHIFT_BITS == 0) ? 0 : $unsigned(shift_amount_in);
    assign safe_shift_amount_int = (shift_amount_extended_int > MAX_SHIFT_VAL) ? MAX_SHIFT_VAL : shift_amount_extended_int;
    if (SHIFT_OP_WIDTH > 0) begin : gen_shift_op_gt0
        assign final_shift_amount = safe_shift_amount_int;
    end else begin : gen_shift_op_eq0
        assign final_shift_amount = '0;
    end
    generate if (DATA_WIDTH > 0) begin : gen_data_width_gt0
        assign output_val = input_val << final_shift_amount;
    end else begin : gen_data_width_eq0
        assign output_val = '0;
    end endgenerate
endmodule
class SimpleClass;
    rand bit [7:0] data;
    function new();
        data = 8'hAA;
    endfunction
    function bit [7:0] get_data;
        return data;
    endfunction
endclass
module SystemVerilogClassModule (
    input wire clk,
    input wire enable,
    output reg [7:0] class_data_out
);
    SimpleClass my_obj;
    always_ff @(posedge clk) begin
        if (my_obj == null) begin
            my_obj = new();
        end
        if (enable && my_obj != null) begin
            class_data_out <= my_obj.get_data();
        end else begin
            class_data_out <= 8'h00;
        end
    end
endmodule
module InoutModule (
    input wire enable,
    inout wire [7:0] data_port,
    output wire data_direction
);
    assign data_port = enable ? ~data_port : 8'bz;
    assign data_direction = enable;
endmodule
module EnumConstModule (
    input wire [1:0] state_in,
    input wire value_in,
    output reg [7:0] data_out
);
    typedef enum { IDLE, RUNNING, DONE } state_t;
    state_t current_state;
    const int MAX_VALUE = 255;
    always_comb begin
        case (state_in)
            2'b00: current_state = IDLE;
            2'b01: current_state = RUNNING;
            2'b10: current_state = DONE;
            default: current_state = IDLE;
        endcase
        if (current_state == RUNNING && value_in) begin
            data_out = MAX_VALUE;
        end else begin
            data_out = 8'h00;
        end
    end
endmodule
module SignedArithmeticModule (
    input signed [7:0] a,
    input signed [7:0] b,
    input wire enable,
    output reg signed [7:0] result
);
    always_comb begin
        if (enable) begin
            result = a + b;
        end else begin
            result = a - b;
        end
    end
endmodule
module DPITestModule (
    input wire [7:0] val_in,
    input wire multiplier_flag,
    output wire [7:0] val_out
);
    assign val_out = val_in * (multiplier_flag ? 2 : 1);
endmodule
module DPISimple (
    input int a,
    input int b,
    output int c
);
    import "DPI-C" function int add_ints(int in1, int in2);
    assign c = add_ints(a, b);
endmodule
module LocalparamModule #(parameter DATA_WIDTH = 8) (
    input wire [DATA_WIDTH-1:0] data_in,
    output wire [DATA_WIDTH-1:0] data_out
);
    localparam int HALF_WIDTH = DATA_WIDTH / 2;
    generate if (DATA_WIDTH > 0) begin : gen_width_gt0
        assign data_out = {data_in[HALF_WIDTH-1:0], data_in[DATA_WIDTH-1:HALF_WIDTH]};
    end else begin : gen_width_eq0
        assign data_out = '0;
    end endgenerate
endmodule
module AlwaysCombFFModule (
    input wire clk,
    input wire reset,
    input wire [7:0] data_in,
    output logic [7:0] data_q,
    output logic [7:0] data_comb
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            data_q <= 8'h00;
        end else begin
            data_q <= data_in;
        end
    end
    always_comb begin
        data_comb = ~data_in;
    end
endmodule
module EnumLogicModule (
    input enum logic [1:0] { S0, S1, S2, S3 } current_state,
    input wire [7:0] data_in,
    output wire [7:0] data_out
);
    assign data_out = data_in + current_state;
endmodule
module AssertionModule (
    input wire clk,
    input wire reset,
    input wire [7:0] data_in,
    input wire check_enable,
    output wire dummy_out
);
    property data_range_prop;
        @(posedge clk) disable iff (reset) (check_enable |-> (data_in >= 8'd10 && data_in <= 8'd20));
    endproperty
    assert property (data_range_prop);
    assign dummy_out = |data_in;
endmodule
module AssertFinalModule (
    input wire check_value,
    output wire dummy_out
);
    assert final (check_value);
    assign dummy_out = check_value;
endmodule
interface MyInterface (input wire clk, input wire reset);
    logic [15:0] data;
    logic req;
    logic ack;
    modport Master (
        output data, req,
        input ack, clk, reset
    );
    modport Slave (
        input data, req, clk, reset,
        output ack
    );
endinterface
module InterfaceUserModule1 (
    MyInterface.Master master_if,
    input wire start_req,
    input wire [15:0] send_data,
    output wire transfer_done
);
    always_ff @(posedge master_if.clk or posedge master_if.reset) begin
        if (master_if.reset) begin
            master_if.req <= 1'b0;
            master_if.data <= 16'b0;
        end else begin
            master_if.data <= send_data;
            master_if.req <= start_req;
        end
    end
    assign transfer_done = master_if.ack;
endmodule
module InterfaceUserModule2 (
    MyInterface.Slave slave_if,
    output wire [15:0] received_data,
    output wire request_received
);
    assign request_received = slave_if.req;
    assign received_data = slave_if.data;
    always_ff @(posedge slave_if.clk or posedge slave_if.reset) begin
        if (slave_if.reset) begin
            slave_if.ack <= 1'b0;
        end else begin
            slave_if.ack <= slave_if.req;
        end
    end
endmodule
interface SystemCInterface (input wire clk_sc, input wire reset_sc);
    logic [31:0] data;
    logic req;
    logic ack;
    modport sc_master (
        output data, req,
        input ack, clk_sc, reset_sc
    );
    modport sc_slave (
        input data, req, clk_sc, reset_sc,
        output ack
    );
endinterface
module SystemCUserModule (
    input wire clk,
    input wire reset,
    SystemCInterface.sc_master master_if,
    output wire dummy_out
);
    always_ff @(posedge master_if.clk_sc or posedge master_if.reset_sc) begin
        if (master_if.reset_sc) begin
            master_if.req <= 1'b0;
            master_if.data <= 32'h0;
        end else begin
            if (master_if.ack) begin
                master_if.req <= 1'b0;
            end else begin
                master_if.req <= 1'b1;
                master_if.data <= master_if.data + 1;
            end
        end
    end
    assign dummy_out = master_if.req | master_if.ack | clk | reset;
endmodule
module SystemCUserSlaveModule (
    input wire clk,
    input wire reset,
    SystemCInterface.sc_slave slave_if,
    output wire [31:0] received_data,
    output wire request_status
);
    always_ff @(posedge slave_if.clk_sc or posedge slave_if.reset_sc) begin
        if (slave_if.reset_sc) begin
            slave_if.ack <= 1'b0;
        end else begin
            slave_if.ack <= slave_if.req;
        end
    end
    assign received_data = slave_if.data;
    assign request_status = slave_if.req | clk | reset;
endmodule
module UnionModule (
    input wire [15:0] data_in,
    input wire select_byte,
    output wire [7:0] byte_out
);
    typedef union {
        logic [15:0] word;
        logic [7:0] bytes [2];
        struct packed {
            logic [7:0] lo;
            logic [7:0] hi;
        } parts;
    } my_union_t;
    my_union_t u_data;
    always_comb begin
        u_data.word = data_in;
        if (select_byte) begin
            byte_out = u_data.bytes[1];
        end else begin
            byte_out = u_data.parts.lo;
        end
    end
endmodule
module GenerateModule #(parameter NUM_STAGES = 4) (
    input wire [NUM_STAGES-1:0] enable_in,
    input wire [NUM_STAGES-1:0] data_in,
    output wire [NUM_STAGES-1:0] data_out
);
    genvar i;
    generate
        for (i = 0; i < NUM_STAGES; i = i + 1) begin : stage_gen
            always_comb begin
                if (enable_in[i]) begin
                    data_out[i] = ~data_in[i];
                end else begin
                    data_out[i] = data_in[i];
                end
            end
        end
    endgenerate
endmodule
module FunctionModule (
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [7:0] out
);
    function automatic [7:0] my_function;
        input [7:0] arg1;
        input [7:0] arg2;
        my_function = arg1 + arg2;
    endfunction
    assign out = my_function(in1, in2);
endmodule
task automatic my_task_standalone;
    input [7:0] arg_in;
    output [7:0] arg_out;
    arg_out = ~arg_in;
endtask
module TaskModule (
    input wire enable,
    input wire [7:0] data_in,
    output reg [7:0] data_out
);
    task automatic my_task_internal;
        input [7:0] arg_in;
        output [7:0] arg_out;
        arg_out = ~arg_in;
    endtask
    always_comb begin
        if (enable) begin
            my_task_internal(data_in, data_out);
        end else begin
            data_out = data_in;
        end
    end
endmodule
module StructModule (
    input wire [15:0] packed_input,
    output wire [7:0] part_a_out,
    output wire [7:0] part_b_out
);
    typedef struct packed {
        logic [7:0] part_a;
        logic [7:0] part_b;
    } my_struct_t;
    my_struct_t s_data;
    assign s_data = packed_input;
    assign part_a_out = s_data.part_a;
    assign part_b_out = s_data.part_b;
endmodule
module CoverageModule (
    input wire [3:0] value_in,
    input wire clock,
    output wire dummy_out
);
    covergroup my_covergroup @(posedge clock);
        coverpoint value_in {
            bins low = {0, 1};
            bins high = {[15:14]};
            bins other = default;
        }
    endgroup
    my_covergroup cg_inst = new();
    assign dummy_out = |value_in;
endmodule
package MyPackage;
    parameter PKG_DATA_WIDTH = 8;
    typedef struct packed {
        logic [PKG_DATA_WIDTH-1:0] data;
        logic valid;
    } packet_t;
endpackage
module PackageUserModule (
    input wire [MyPackage::PKG_DATA_WIDTH-1:0] input_data,
    input wire input_valid,
    output wire [MyPackage::PKG_DATA_WIDTH-1:0] output_data,
    output wire output_valid
);
    import MyPackage::*;
    packet_t my_packet;
    assign my_packet.data = input_data;
    assign my_packet.valid = input_valid;
    assign output_data = my_packet.data;
    assign output_valid = my_packet.valid;
endmodule
module MainDesign (
    input wire clk,
    input wire reset,
    input wire enable_main,
    input wire [15:0] data_in_main,
    output wire [15:0] data_out_main
);
    wire child_enable_wire;
    wire [15:0] child_data_out_wire;
    wire [7:0] mux_data_out_wire;
    reg [15:0] seq_reg;
    wire simple_and_out;
    wire [7:0] complex_vec_out;
    wire complex_scalar_out;
    integer integer_out_wire;
    wire [7:0] memory_read_data_wire;
    wire [16-1:0] loop_data_out_wire;
    wire [16-1:0] parameterized_output_wire;
    wire [7:0] function_out_wire;
    wire [7:0] task_data_out_wire;
    wire [7:0] struct_part_a_out_wire;
    wire [7:0] struct_part_b_out_wire;
    wire coverage_dummy_out_wire;
    wire [7:0] class_data_out_wire;
    wire [7:0] inout_wire;
    wire inout_direction_wire;
    reg drive_inout;
    reg [7:0] data_to_drive;
    wire [7:0] data_read_from_inout;
    wire [7:0] enum_const_out_wire;
    wire signed [7:0] signed_arith_out_wire;
    reg [7:0] internal_data_array [0:7];
    wire [7:0] dpit_out_wire;
    wire [16-1:0] localparam_out_wire;
    wire [7:0] always_q_out_wire;
    wire [7:0] always_comb_out_wire;
    enum logic [1:0] { S0, S1, S2, S3 } enum_logic_state_wire;
    wire [7:0] enum_logic_out_wire;
    wire assertion_dummy_out_wire;
    wire assert_final_dummy_out_wire;
    wire if_transfer_done_wire;
    wire [15:0] if_received_data_wire;
    wire if_request_received_wire;
    wire [7:0] union_byte_out_wire;
    wire systemc_dummy_out_wire;
    wire [31:0] sc_received_data_wire;
    wire sc_request_status_wire;
    wire [3:0] generate_enable_wire;
    wire [3:0] generate_data_in_wire;
    wire [3:0] generate_data_out_wire;
    integer dpi_simple_out_wire;
    wire [7:0] pkg_user_data_out_wire;
    wire pkg_user_valid_out_wire;
    MyInterface if_inst (
        .clk(clk),
        .reset(reset)
    );
    SystemCInterface sc_if_inst (
        .clk_sc(clk),
        .reset_sc(reset)
    );
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (int i = 0; i < 8; i++) internal_data_array[i] <= 8'h00;
            seq_reg <= 16'b0;
            drive_inout <= 1'b0;
            data_to_drive <= 8'h00;
            generate_enable_wire <= 4'b0;
            generate_data_in_wire <= 4'b0;
        end else begin
            for (int i = 0; i < 8; i++) internal_data_array[i] <= data_in_main[7:0] + i;
            seq_reg <= data_in_main + child_data_out_wire + {8'b0, mux_data_out_wire};
            drive_inout <= enable_main & ~inout_direction_wire;
            data_to_drive <= data_in_main[7:0];
            generate_enable_wire <= {enable_main, enable_main, enable_main, enable_main};
            generate_data_in_wire <= data_in_main[3:0];
        end
    end
    assign enum_logic_state_wire = data_in_main[1:0];
    HierChild hc_inst (
        .child_enable(enable_main),
        .child_data_in(data_in_main),
        .child_data_out(child_data_out_wire)
    );
    MuxCase mc_inst (
        .sel(data_in_main[1:0]),
        .data_a(data_in_main[7:0]),
        .data_b(data_in_main[15:8]),
        .data_c({data_in_main[15:8], data_in_main[7:0]}),
        .data_out(mux_data_out_wire)
    );
    BasicSequential bs_inst (
        .clk(clk),
        .d_in(reset ? 1'b0 : enable_main),
        .q_out(child_enable_wire)
    );
    SimpleCombinational sc_inst (
        .in1(enable_main),
        .in2(reset),
        .out_and(simple_and_out)
    );
    ComplexCombinational cc_inst (
        .condition(enable_main),
        .data_a(data_in_main[7:0]),
        .data_b(data_in_main[15:8]),
        .index(data_in_main[2:0]),
        .data_array(internal_data_array),
        .result_vec(complex_vec_out),
        .result_scalar(complex_scalar_out)
    );
    IntegerModule im_inst (
        .int_in1($signed(data_in_main[7:0])),
        .int_in2($signed(data_in_main[15:8])),
        .scalar_in(enable_main),
        .int_out(integer_out_wire)
    );
    MemoryModule mm_inst (
        .clk(clk),
        .write_en(enable_main & ~reset),
        .addr(data_in_main[3:0]),
        .write_data(data_in_main[7:0]),
        .read_data(memory_read_data_wire)
    );
    LoopModule #(.WIDTH(16)) lm_inst (
        .data_in(data_in_main),
        .enable(enable_main),
        .data_out(loop_data_out_wire)
    );
    ParameterizedModule #(.DATA_WIDTH(16), .SHIFT_MAX(8)) pm_inst (
        .input_val(data_in_main),
        .shift_amount_in(data_in_main[$clog2(8)-1:0]),
        .output_val(parameterized_output_wire)
    );
    FunctionModule fm_inst (
        .in1(data_in_main[7:0]),
        .in2(data_in_main[15:8]),
        .out(function_out_wire)
    );
    TaskModule tm_inst (
        .enable(enable_main),
        .data_in(data_in_main[7:0]),
        .data_out(task_data_out_wire)
    );
    StructModule stm_inst (
        .packed_input(data_in_main),
        .part_a_out(struct_part_a_out_wire),
        .part_b_out(struct_part_b_out_wire)
    );
    CoverageModule covm_inst (
        .value_in(data_in_main[3:0]),
        .clock(clk),
        .dummy_out(coverage_dummy_out_wire)
    );
    SystemVerilogClassModule svcm_inst (
        .clk(clk),
        .enable(enable_main),
        .class_data_out(class_data_out_wire)
    );
    InoutModule iom_inst (
        .enable(enable_main),
        .data_port(inout_wire),
        .data_direction(inout_direction_wire)
    );
    assign inout_wire = drive_inout ? data_to_drive : 8'bz;
    assign data_read_from_inout = inout_wire;
    EnumConstModule ecm_inst (
        .state_in(data_in_main[1:0]),
        .value_in(enable_main),
        .data_out(enum_const_out_wire)
    );
    SignedArithmeticModule sam_inst (
        .a($signed(data_in_main[7:0])),
        .b($signed(data_in_main[15:8])),
        .enable(enable_main),
        .result(signed_arith_out_wire)
    );
    DPITestModule dpitm_inst (
        .val_in(data_in_main[7:0]),
        .multiplier_flag(enable_main),
        .val_out(dpit_out_wire)
    );
    DPISimple dpisim_inst (
        .a($signed(data_in_main[7:0])),
        .b($signed(data_in_main[15:8])),
        .c(dpi_simple_out_wire)
    );
    LocalparamModule #(.DATA_WIDTH(16)) lpm_inst (
        .data_in(data_in_main),
        .data_out(localparam_out_wire)
    );
    AlwaysCombFFModule acffm_inst (
        .clk(clk),
        .reset(reset),
        .data_in(data_in_main[7:0]),
        .data_q(always_q_out_wire),
        .data_comb(always_comb_out_wire)
    );
    EnumLogicModule elm_inst (
        .current_state(enum_logic_state_wire),
        .data_in(data_in_main[7:0]),
        .data_out(enum_logic_out_wire)
    );
    AssertionModule assertm_inst (
        .clk(clk),
        .reset(reset),
        .data_in(data_in_main[7:0]),
        .check_enable(enable_main),
        .dummy_out(assertion_dummy_out_wire)
    );
     AssertFinalModule afm_inst (
        .check_value(enable_main),
        .dummy_out(assert_final_dummy_out_wire)
    );
    InterfaceUserModule1 ium1_inst (
        .master_if(if_inst.Master),
        .start_req(enable_main),
        .send_data(data_in_main),
        .transfer_done(if_transfer_done_wire)
    );
    InterfaceUserModule2 ium2_inst (
        .slave_if(if_inst.Slave),
        .received_data(if_received_data_wire),
        .request_received(if_request_received_wire)
    );
    UnionModule unionm_inst (
        .data_in(data_in_main),
        .select_byte(enable_main),
        .byte_out(union_byte_out_wire)
    );
    SystemCUserModule sc_master_inst (
        .clk(clk),
        .reset(reset),
        .master_if(sc_if_inst.sc_master),
        .dummy_out(systemc_dummy_out_wire)
    );
    SystemCUserSlaveModule sc_slave_inst (
        .clk(clk),
        .reset(reset),
        .slave_if(sc_if_inst.sc_slave),
        .received_data(sc_received_data_wire),
        .request_status(sc_request_status_wire)
    );
    GenerateModule #(.NUM_STAGES(4)) genm_inst (
        .enable_in(generate_enable_wire),
        .data_in(generate_data_in_wire),
        .data_out(generate_data_out_wire)
    );
    PackageUserModule pkg_user_inst (
        .input_data(data_in_main[7:0]),
        .input_valid(enable_main),
        .output_data(pkg_user_data_out_wire),
        .output_valid(pkg_user_valid_out_wire)
    );
    assign data_out_main = seq_reg
                           ^ child_data_out_wire
                           ^ {8'b0, mux_data_out_wire}
                           ^ {8'b0, complex_vec_out}
                           ^ {8'b0, $unsigned(integer_out_wire[7:0])}
                           ^ {8'b0, memory_read_data_wire}
                           ^ loop_data_out_wire
                           ^ parameterized_output_wire
                           ^ {8'b0, function_out_wire}
                           ^ {8'b0, task_data_out_wire}
                           ^ {8'b0, struct_part_a_out_wire}
                           ^ {8'b0, struct_part_b_out_wire}
                           ^ {8'b0, data_read_from_inout}
                           ^ {8'b0, enum_const_out_wire}
                           ^ {8'b0, $unsigned(signed_arith_out_wire)}
                           ^ {8'b0, dpit_out_wire}
                           ^ {8'b0, $unsigned(dpi_simple_out_wire[7:0])}
                           ^ localparam_out_wire
                           ^ {8'b0, always_q_out_wire}
                           ^ {8'b0, always_comb_out_wire}
                           ^ {8'b0, enum_logic_out_wire}
                           ^ {{15{1'b0}}, assertion_dummy_out_wire}
                           ^ {{15{1'b0}}, assert_final_dummy_out_wire}
                           ^ if_received_data_wire
                           ^ {8'b0, union_byte_out_wire}
                           ^ {{15{1'b0}}, systemc_dummy_out_wire}
                           ^ sc_received_data_wire[15:0]
                           ^ {{15{1'b0}}, sc_request_status_wire}
                           ^ {12'b0, generate_data_out_wire}
                           ^ {8'b0, pkg_user_data_out_wire}
                           ^ {{15{1'b0}}, pkg_user_valid_out_wire};
endmodule

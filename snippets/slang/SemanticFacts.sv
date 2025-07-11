`timescale 1ns/1ps
module ModuleDefinition (
    input  wire in_md,
    output logic out_md
);
    assign out_md = in_md;
endmodule
interface InterfaceDefinition;
    logic [7:0] data;
    logic       enable;
    logic       clk_if;
    logic       rst_if;
    logic [3:0] value_if;
    task automatic interface_task(input int value);
    endtask
    function automatic int interface_func(input int value);
        interface_func = value + 1;
    endfunction
    clocking if_cb @(posedge clk_if);
        input  data;
        output enable;
        input  rst_if;
        output value_if;
    endclocking
    modport master (
        output data,
        output enable,
        import task interface_task(input int value),
        import function int interface_func(input int value)
    );
    modport slave (
        input  data,
        input  enable,
        export task interface_task(input int value),
        export function int interface_func(input int value)
    );
endinterface
module ProgramDefinition (
    input  wire in_pd,
    output logic out_pd
);
    assign out_pd = in_pd;
endmodule
module VariableLifetimeAndProceduralBlocks (
    input  wire        clk,
    input  wire        rst,
    input  wire [7:0]  data_in,
    input  wire        edge_sig,
    output logic [7:0] data_out_comb,
    output logic [7:0] data_out_ff,
    output logic       out_toggle_always,
    output logic       out_toggle_edge,
    output int         static_count_out
);
    static integer static_counter = 0;
    logic [7:0] ff_reg_data;
    logic [7:0] latch_reg_data;
    static logic explicit_static_var = 1'b0;
    final begin end
    always_comb begin
        data_out_comb = ff_reg_data + 1;
    end
    always_ff @(posedge clk or negedge rst) begin
        automatic int auto_ff_var = 5;
        if (!rst) begin
            ff_reg_data       <= 8'h00;
            static_counter    = 0;
            out_toggle_always <= 1'b0;
        end
        else begin
            ff_reg_data       <= data_in + auto_ff_var;
            static_counter    = static_counter + 1;
            out_toggle_always <= ~out_toggle_always;
        end
        data_out_ff      <= ff_reg_data;
        static_count_out <= static_counter;
    end
    always_latch begin
        automatic int auto_latch_var = 3;
        if (data_in > 10)
            latch_reg_data = data_in + auto_latch_var;
    end
    always @(posedge edge_sig or negedge edge_sig) begin
        automatic int auto_edge_var = 2;
        out_toggle_edge  <= ~out_toggle_edge;
    end
    task automatic my_task_auto(input int count, ref logic [7:0] data);
        automatic int task_local_var;
        task_local_var = count * 2;
        data           = data + task_local_var;
    endtask
    function automatic int my_func_auto(input int count);
        automatic int func_local_var;
        func_local_var = count * 3;
        return func_local_var;
    endfunction
endmodule
module PortAndArgumentDirections (
    input  logic [3:0] in_dir,
    output logic [3:0] out_dir,
    inout  wire  [3:0] io_dir
);
    logic [3:0] internal_io;
    assign io_dir = (in_dir > 4) ? internal_io : 4'bz;
    always_comb begin
        internal_io = in_dir + 1;
        out_dir     = internal_io;
    end
    task automatic check_ref(ref logic [3:0] data);
        data = data * 2;
    endtask
endmodule
module TypeDeclarationsAndRestrictions (
    input  wire [7:0] in_val,
    output logic [7:0] out_val
);
    typedef enum logic [1:0] {STATE_IDLE = 0, STATE_BUSY = 1, STATE_DONE = 2} my_enum_t;
    typedef struct packed {logic [3:0] field1; logic [3:0] field2;} my_struct_t;
    typedef struct {int unpacked_f1; int unpacked_f2;} my_unpacked_struct_t;
    typedef union packed {logic [7:0] byte_val; my_struct_t fields;} my_union_t;
    typedef union {longint unpacked_u_l; int unpacked_u_i;} my_unpacked_union_t;
    interface class MyInterfaceClass;
        pure virtual function int get_id();
    endclass
    typedef class ForwardClass;
    typedef interface class ForwardIfaceClass;
    typedef enum {FWD_E1} ForwardEnum;
    typedef struct packed {int field;} ForwardStruct_t;
    typedef union  packed {int field;} ForwardUnion_t;
    class ForwardClass;
        int field;
        function new(); endfunction
    endclass
    interface class ForwardIfaceClass;
        pure virtual function void dummy_func();
    endclass
    my_struct_t           s_var;
    my_unpacked_struct_t  us_var;
    my_union_t            u_var;
    my_unpacked_union_t   uu_var;
    my_enum_t             e_var;
    ForwardStruct_t       fwd_struct_var;
    ForwardUnion_t        fwd_union_var;
    ForwardEnum           fwd_enum_var;
    assign out_val = in_val;
endmodule
module AssertionsAndElabTasks (
    input  wire        clk,
    input  wire        reset,
    input  wire        condition_a,
    input  wire [1:0]  state_in,
    output logic       dummy_out
);
    always_comb begin
        dummy_out = condition_a;
        if (condition_a) begin
            assert (state_in != 2'b11) else $error("Invalid state 11 detected");
            assume (state_in != 2'b00);
            cover  (state_in == 2'b01);
        end
    end
    property p_valid_state;
        @(posedge clk) !reset |-> (state_in != 2'b10);
    endproperty
    assert property (p_valid_state);
    assume property (@(posedge clk) state_in != 2'b00);
    cover  property (p_valid_state);
    restrict property (@(posedge clk) !reset);
endmodule
module StrengthsAndChargeStrength (
    input  wire in_data_s,
    output wire out_data_s
);
    wire (supply1, supply0) drive_wire_sup = in_data_s;
    wire (strong1, weak0)   drive_wire_sw  = in_data_s;
    wire (weak0,  strong1)  drive_wire_ws  = !in_data_s;
    wire (pull0,  weak1)    drive_wire_p0w = in_data_s;
    wire (weak0,  pull1)    drive_wire_wp1 = !in_data_s;
    wire (highz0, weak1)    drive_wire_hz0w = in_data_s;
    wire (weak0,  highz1)   drive_wire_whz1 = !in_data_s;
    wire (pull0,  pull1)    pull_wire0 = in_data_s;
    wire (pull1,  pull0)    pull_wire1 = !in_data_s;
    trireg (small)  tri_small  = in_data_s;
    trireg (medium) tri_medium = !in_data_s;
    trireg (large)  tri_large  = in_data_s | !in_data_s;
    trireg          tri_default = 1'b1;
    assign out_data_s = drive_wire_sup | drive_wire_sw | drive_wire_ws | drive_wire_p0w |
                        drive_wire_wp1 | drive_wire_hz0w | drive_wire_whz1 | pull_wire0 |
                        pull_wire1 | tri_medium | tri_small | tri_large | tri_default;
endmodule
module SequentialAndParallelBlocks (
    input  wire        start_sig,
    input  wire [7:0]  data_in_pb,
    output logic [7:0] result_join,
    output logic [7:0] result_join_any,
    output logic [7:0] result_join_none,
    output logic [7:0] result_seq
);
    always @(posedge start_sig) begin
        automatic int local_var = 1;
        begin
            result_seq = data_in_pb + local_var - 1;
        end
        fork
            result_join = data_in_pb + 1;
            result_join = (data_in_pb + 1) & 8'hFF;
        join
        fork
            result_join_any = data_in_pb + 2;
            result_join_any = (data_in_pb + 2) * 3;
        join_any
        fork
            result_join_none = data_in_pb + 4;
            result_join_none = (data_in_pb + 4) | 8'hAA;
        join_none
    end
endmodule
module ClockingBlockAndModportItems (
    input  logic       clk_cb,
    input  logic       rst_cb,
    input  logic [7:0] data_in_cb,
    input  logic       internal_sig_cb_in,
    output logic [7:0] data_out_cb
);
    logic [3:0] internal_data_cb;
    logic [3:0] cb_input_data;
    logic       cb_output_sig;
    logic [3:0] cb_output_data;
    logic       internal_sig_derived;
    assign internal_sig_derived = data_in_cb[7] | internal_sig_cb_in;
    assign cb_input_data        = data_in_cb[3:0];
    clocking cb @(posedge clk_cb);
        input  cb_input_data;
        input  internal_sig_derived;
        output cb_output_data;
        output cb_output_sig;
    endclocking
    always @(posedge clk_cb) begin
        internal_data_cb  = cb_input_data + (internal_sig_derived ? 1 : 0);
        cb_output_data   <= internal_data_cb;
        cb_output_sig    <= internal_data_cb[0];
    end
    assign data_out_cb = {4'b0000, cb_output_data};
endmodule
module TimeScaleDeclarationModule (
    input  logic dummy_in_ts,
    output logic dummy_out_ts
);
    timeunit      10ns;
    timeprecision 100ps;
    assign dummy_out_ts = dummy_in_ts;
endmodule
`timescale 100ps/10ps
module ImplicitTimeScaleModule (
    input  logic in_its,
    output logic out_its
);
    assign out_its = in_its;
endmodule
`timescale 1ns/1ps
module ValidTimeScaleModuleDecl (
    input  logic in_vts,
    output logic out_vts
);
    timeunit      1ns;
    timeprecision 1ps;
    assign out_vts = in_vts;
endmodule
module CaseStatementConditions (
    input  wire [1:0] selector,
    input  wire [3:0] data_c,
    output logic [3:0] out_case
);
    always_comb begin
        case (selector)
            2'b00: out_case = data_c;
            2'b01: out_case = data_c + 1;
            2'b10: out_case = data_c + 2;
            default: out_case = 4'bxxxx;
        endcase
        casez (selector)
            2'b0?: out_case = data_c + 10;
            2'b1?: out_case = data_c + 20;
            default: out_case = 4'bzzzz;
        endcase
        casex (selector)
            2'b0?: out_case = data_c - 1;
            2'b1?: out_case = data_c - 2;
            default: out_case = 4'bxxxx;
        endcase
    end
endmodule
module PulseStyleModule (
    input  wire clk,
    input  wire data_in_ps,
    output wire data_out_ps
);
    reg ff_q;
    always @(posedge clk) begin
        ff_q <= data_in_ps;
    end
    assign data_out_ps = ff_q;
    specify
        pulsestyle_ondetect data_out_ps;
        showcancelled        data_out_ps;
        (data_in_ps => data_out_ps) = (1, 1);
    endspecify
endmodule

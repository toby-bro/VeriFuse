`timescale 1ns/1ps
timeunit 1ns;
timeprecision 1ps;
int compilation_unit_var = 10;
`define HASH_MINUS_HASH #-#
`define HASH_EQUALS_HASH #=#
typedef logic [3:0] my_custom_net_t;
module Module_CovergroupHost (input bit clk, input int data_in_cg, output bit cover_out_cg);
    covergroup cg @(posedge clk);
        cp1: coverpoint data_in_cg {
            bins low  = { [0:10] };
            bins high = { [5:15] };
            ignore_bins zero = {0};
            illegal_bins bad = {30};
        }
    endgroup
    cg cg_inst = new();
    assign cover_out_cg = 1'b0;
endmodule
module Module_BasicSyntax (
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic [7:0] out_ops,
    output logic       out_cmp
);
    logic [7:0] temp;
    always_comb begin
        temp = in_a + in_b;
    end
    assign out_ops = (in_a & in_b) | (in_a ^ in_b);
    assign out_cmp = (in_a == in_b);
endmodule
module Module_DataTypes (
    input  int  int_in,
    output int  int_out,
    input  bit  esc_in,
    output bit  esc_out,
    output int  pkg_func_out,
    output int  chandle_null
);
    import my_package::*;
    chandle my_ch;
    assign int_out       = int_in + my_package::PKG_PARAM;
    assign pkg_func_out  = my_package::pkg_func();
    assign esc_out       = esc_in;
    assign chandle_null  = my_ch == null;
endmodule
package my_package;
    parameter int PKG_PARAM = 1;
    function automatic int pkg_func(); return PKG_PARAM; endfunction
endpackage
module Module_NetTypes_Strengths (
    input  bit            drive_in,
    output wire           uwire_out,
    output wire           tri_out,
    output wire           tri0_out,
    output wire           tri1_out,
    output wire           triand_out,
    output wire           trior_out,
    output wire           trireg_out,
    output wire           wand_out,
    output wire           wor_out,
    output wire           pulldown_out,
    output wire           pullup_out,
    output logic          scalared_out,
    output my_custom_net_t custom_net_out
);
    uwire    my_uwire;
    tri      my_tri;
    tri0     my_tri0;
    tri1     my_tri1;
    triand   my_triand;
    trior    my_trior;
    trireg   my_trireg;
    wand     my_wand;
    wor      my_wor;
    wire     pulldown_internal;
    wire     pullup_internal;
    wire     scalar_wire;
    my_custom_net_t custom_net_internal;
    pulldown pd_drv(pulldown_internal);
    pullup   pu_drv(pullup_internal);
    assign my_uwire          = drive_in;
    assign my_tri            = drive_in;
    assign my_tri0           = drive_in;
    assign my_tri1           = drive_in;
    assign my_triand         = drive_in;
    assign my_trior          = drive_in;
    assign my_trireg         = drive_in;
    assign my_wand           = drive_in;
    assign my_wor            = drive_in;
    assign uwire_out         = my_uwire;
    assign tri_out           = my_tri;
    assign tri0_out          = my_tri0;
    assign tri1_out          = my_tri1;
    assign triand_out        = my_triand;
    assign trior_out         = my_trior;
    assign trireg_out        = my_trireg;
    assign wand_out          = my_wand;
    assign wor_out           = my_wor;
    assign pulldown_out      = pulldown_internal;
    assign pullup_out        = pullup_internal;
    assign scalar_wire       = drive_in;
    assign scalared_out      = scalar_wire;
    assign custom_net_internal = drive_in ? 4'b1111 : 4'b0000;
    assign custom_net_out      = custom_net_internal;
endmodule
module Module_ControlFlow (
    input  logic [2:0] sel_in,
    input  logic [7:0] data_in,
    input  bit         clk,
    input  bit         reset_n,
    output reg  [7:0]  data_out
);
    reg [7:0] temp;
    always_comb begin
        unique case (sel_in)
            3'b000: temp = data_in;
            3'b001: temp = data_in + 1;
            3'b010: temp = data_in - 1;
            default: temp = 8'hAA;
        endcase
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            data_out <= 8'h00;
        else
            data_out <= temp;
    end
endmodule
module Module_ProceduralCode (
    input  int    in1,
    input  int    in2,
    output int    add_out
);
    function automatic int add_func(input int a, b);
        return a + b;
    endfunction
    assign add_out = add_func(in1, in2);
endmodule
module Module_GatePrimitives (
    input  wire g_in,
    input  wire g_ctrl_n,
    input  wire g_ctrl_p,
    output wire g_out_and,
    output wire g_out_or
);
    and a1 (g_out_and, g_in, g_in);
    or  o1 (g_out_or , g_in, g_in);
endmodule
module Module_Assertions (
    input  logic assert_in,
    input  bit   clk,
    output logic assert_out
);
    property p1; @(posedge clk) assert_in |-> ##1 assert_in; endproperty
    assert property (p1);
    assign assert_out = assert_in;
endmodule
module BindSimpleModule (input bit in, output bit out);
    assign out = in;
endmodule
module DummyBindTarget (input bit d_in, output bit d_out);
    assign d_out = d_in;
    BindSimpleModule u_bind (.in(d_in), .out());
endmodule
module Module_SVKeywords (
    input  bit [7:0] in_sv,
    output bit [7:0] out_sv
);
    assign out_sv = (in_sv inside {8'd1,8'd2,8'd3}) ? 8'hAA : 8'h55;
endmodule
module Module_MacroTokens (
    input  logic tok_in,
    output logic tok_out
);
    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = tok_in;
        tok_out         = `PASTE(my,_var);
    end
endmodule
module Module_UntypedParam #(
    parameter type T = int
) (
    input  T in_p,
    output T out_p
);
    assign out_p = in_p;
endmodule
module Module_IfNoneParam (
    input  int in_port,
    output int out_port
);
    assign out_port = in_port;
endmodule
module Module_ConfigKeywords (
    input  bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule
module TopConfigExample (
    input  bit in_tc,
    output bit out_tc
);
    Module_ConfigKeywords i_cfg (.cfg_in(in_tc), .cfg_out(out_tc));
endmodule
module Module_Hierarchical (
    input  bit h_in,
    output bit h_out
);
    int cu_var_read;
    assign h_out = h_in;
    always_comb begin
        cu_var_read = $unit::compilation_unit_var;
    end
endmodule

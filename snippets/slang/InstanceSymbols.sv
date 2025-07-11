module mod_basic #(
  parameter int P1 = 10,
  parameter type T1 = logic
) (
  input logic in1,
  input T1 in2,
  output logic out1,
  output T1 out2
);
  assign out1 = in1;
  assign out2 = in2;
endmodule
module mod_large_array_target (
  input logic in_la,
  output logic out_la
);
  assign out_la = in_la;
endmodule
module mod_arrays (
  input logic [7:0] in_vec,
  input logic in_large,
  output logic [7:0] out_vec,
  output logic out_large
);
  wire [7:0] basic_out1_vec;
  wire [7:0] basic_out2_vec;
  wire large_out_vec [0:7];
  mod_basic #(.P1(8)) basic_inst_array [7:0] (
    .in1(in_vec),
    .in2(in_vec),
    .out1(basic_out1_vec),
    .out2(basic_out2_vec)
  );
  mod_large_array_target large_inst_array [0:7] (
    .in_la(in_large),
    .out_la(large_out_vec)
  );
  assign out_vec = basic_out1_vec | basic_out2_vec;
  assign out_large = large_out_vec[0];
endmodule
module mod_implicit (
  input logic in_implicit,
  output logic out_implicit
);
  wire implicit_out1;
  wire implicit_out2;
  mod_basic #(.P1(1)) implicit_inst (
    .in1(in_implicit),
    .in2(in_implicit),
    .out1(implicit_out1),
    .out2(implicit_out2)
  );
  assign out_implicit = implicit_out1 | implicit_out2;
endmodule
module mod_prims (
  input wire p_in1,
  input wire p_in2,
  input wire p_control,
  inout wire p_bidi_inout1,
  inout wire p_bidi_inout2,
  output wire p_out1,
  output wire p_out2,
  output wire p_bidi_out,
  output wire p_pull_out
);
  wire prim_out1;
  wire prim_out2;
  wire prim_out3;
  wire prim_out4;
  wire prim_out5;
  wire prim_out6;
  wire prim_out7;
  wire prim_out8;
  wire prim_out9;
  wire prim_out10;
  wire prim_out11;
  wire prim_out12;
  wire prim_out13;
  wire prim_out14;
  wire prim_out15;
  wire prim_out16;
  wire prim_out17;
  wire [1:0] prim_out_array;
  wire pull_out1;
  wire pull_out2;
  assign p_out1 = prim_out1 | prim_out3 | prim_out4 | prim_out5 | prim_out6 | prim_out_array[0] | prim_out15;
  assign p_out2 = prim_out2 | prim_out_array[1] | pull_out2 | prim_out16 | prim_out17;
  assign p_bidi_out = prim_out7 | prim_out8 | prim_out9 | prim_out10 | prim_out11 | prim_out12 | prim_out13 | prim_out14 | pull_out1;
  assign p_pull_out = pull_out1 | pull_out2;
  and a1 (prim_out1, p_in1, p_in2);
  or o1 (prim_out2, p_in1, p_in2);
  xor x1 (prim_out3, p_in1, p_in2);
  xnor xn1 (prim_out15, p_in1, p_in2);
  buf #(1) b1 (prim_out4, p_in1);
  not #(2,3) n1 (prim_out5, p_in1);
  nand #(4) na1 (prim_out6, p_in1, p_in2);
  nor no1 (prim_out16, p_in1, p_in2);
  bufif0 bi01 (prim_out13, p_in1, p_control);
  bufif1 bi11 (prim_out14, p_in1, p_control);
  notif0 ni01 (prim_out17, p_in1, p_control);
  notif1 ni11 (prim_out1, p_in1, p_control);
  tran t1 (p_bidi_inout1, p_bidi_inout2);
  rtran rt1 (p_bidi_inout1, p_bidi_inout2);
  tranif1 ti1 (p_bidi_inout1, p_bidi_inout2, p_control);
  tranif0 ti0 (p_bidi_inout1, p_bidi_inout2, p_control);
  rtranif1 rti1 (p_bidi_inout1, p_bidi_inout2, p_control);
  rtranif0 rti0 (p_bidi_inout1, p_bidi_inout2, p_control);
  cmos cm1 (prim_out7, p_bidi_inout1, p_bidi_inout2, p_control);
  rcmos rcm1 (prim_out8, p_bidi_inout1, p_bidi_inout2, p_control);
  nmos nm1 (prim_out9, p_bidi_inout1, p_control);
  pmos pm1 (prim_out10, p_bidi_inout1, p_control);
  rnmos rnmos1 (prim_out11, p_bidi_inout1, p_control);
  rpmos rpmos1 (prim_out12, p_bidi_inout1, p_control);
  pullup pu1 (pull_out1);
  pulldown pd1 (pull_out2);
  and prim_inst_array [1:0] (
    prim_out_array[0],
    p_in1, p_in2
  );
  and prim_inst_array_idx [1:0] (
    prim_out_array[1],
    p_in1, p_in2
  );
endmodule
primitive my_udp (z, a, b);
  output z;
  input a, b;
  table
    0 0 : 0;
    0 1 : 1;
    1 0 : 1;
    1 1 : 0;
  endtable
endprimitive
module mod_udp (
  input logic u_in1,
  input logic u_in2,
  output wire u_out
);
  wire udp_out1;
  wire [1:0] udp_array_out;
  my_udp udp_inst (udp_out1, u_in1, u_in2);
  my_udp udp_array [1:0] (
    udp_array_out[0],
    u_in1,
    u_in2
  );
  assign u_out = udp_out1 | udp_array_out[0];
endmodule
function automatic int my_func(input int i);
  return i + 1;
endfunction
checker my_checker (
  input logic clk,
  input logic reset,
  input logic c_in1,
  input logic c_in2,
  output logic c_out_comb,
  output logic c_out_ff = 1'b0
);
  logic internal_var_comb;
  logic internal_var_ff;
  logic temp_var;
  always_comb begin : comb_block_chk
    internal_var_comb = c_in1 | c_in2;
    temp_var = internal_var_comb & c_in1;
    if (reset) begin
      temp_var = 0;
    end else begin
      case (c_in1)
        1'b0: temp_var = my_func(0);
        1'b1: temp_var = my_func(temp_var);
        default: temp_var = 0;
      endcase
      while (temp_var < 5) begin
          temp_var = temp_var + 1;
      end
    end
  end
  always_ff @(posedge clk) begin : ff_block_chk
    internal_var_ff <= c_in1;
    if (internal_var_ff) internal_var_ff <= my_func(internal_var_ff);
  end
  always_latch begin : latch_block_chk
  end
  final begin : final_block_chk
  end
  assert_immed: assert property (@(posedge clk) disable iff (reset) c_in1 |-> c_out_comb);
  assign c_out_comb = internal_var_comb;
  assign c_out_ff = internal_var_ff;
endchecker
module mod_checker_inst (
  input wire clk,
  input wire reset,
  input logic ch_in1,
  input logic ch_in2,
  output wire ch_out_comb_named,
  output wire ch_out_ff_named,
  output wire ch_out_comb_ordered,
  output wire ch_out_ff_ordered,
  output wire [1:0] ch_out_comb_array,
  output wire [1:0] ch_out_ff_array,
  output logic ch_out_comb_proc,
  output logic ch_out_ff_proc
);
  my_checker checker_inst_named (
    .clk(clk),
    .reset(reset),
    .c_in1(ch_in1),
    .c_in2(ch_in2),
    .c_out_comb(ch_out_comb_named),
    .c_out_ff(ch_out_ff_named)
  );
  my_checker checker_inst_ordered (
    clk,
    reset,
    ch_in1,
    ch_in2,
    ch_out_comb_ordered,
    ch_out_ff_ordered
  );
  my_checker checker_array [1:0] (
    .clk(clk),
    .reset(reset),
    .c_in1(ch_in1),
    .c_in2(ch_in2),
    .c_out_comb(ch_out_comb_array),
    .c_out_ff(ch_out_ff_array)
  );
  always @(posedge clk) begin : proc_block_for_checker_inst
    static logic proc_clk = clk;
    static logic proc_reset = reset;
    static logic proc_ch_in1 = ch_in1;
    static logic proc_ch_in2 = ch_in2;
    my_checker procedural_checker_inst (
      .clk(proc_clk),
      .reset(proc_reset),
      .c_in1(proc_ch_in1),
      .c_in2(proc_ch_in2),
      .c_out_comb(ch_out_comb_proc),
      .c_out_ff(ch_out_ff_proc)
    );
  end
endmodule
module mod_uninstantiated #(parameter P_UNINST = 0) (
  input wire uninst_in,
  output wire uninst_out
);
  wire basic_out1;
  wire basic_out2;
  logic uninst_chk_out_comb, uninst_chk_out_ff;
  generate if (P_UNINST == 0) begin : gen_inst
    mod_basic #(.P1(1)) instantiated_mod_inst (
      .in1(uninst_in),
      .in2(uninst_in),
      .out1(basic_out1),
      .out2(basic_out2)
    );
  end else begin : gen_empty_mod
  end endgenerate
  generate if (P_UNINST == 0) begin : gen_prim
    and instantiated_prim_inst (uninst_out, uninst_in, uninst_in);
  end else begin : gen_empty_prim
  end endgenerate
  generate if (P_UNINST == 1) begin : gen_checker_instantiated
    my_checker instantiated_chk_inst (
      .clk(uninst_in),
      .reset(uninst_in),
      .c_in1(uninst_in),
      .c_in2(uninst_in),
      .c_out_comb(uninst_chk_out_comb),
      .c_out_ff(uninst_chk_out_ff)
    );
    assign uninst_out = uninst_chk_out_comb | uninst_chk_out_ff;
  end else begin : gen_checker_uninstantiated
  end endgenerate
endmodule
module mod_uninstantiated_container (
  input wire uc_in,
  output wire uc_out_inst,
  output wire uc_out_uninst
);
  mod_uninstantiated #(.P_UNINST(0)) uninst_instantiated (.uninst_in(uc_in), .uninst_out(uc_out_inst));
  mod_uninstantiated #(.P_UNINST(1)) uninst_uninstantiated (.uninst_in(uc_in), .uninst_out(uc_out_uninst));
endmodule
module mod_attributes (
  input logic attr_in,
  output wire attr_out
);
  wire basic_out1;
  wire basic_out2;
  wire prim_out;
  logic checker_out_comb, checker_out_ff;
  (* foo = "bar" *)
  mod_basic #(.P1(1)) basic_attr_inst (
    .in1(attr_in),
    .in2(attr_in),
    .out1(basic_out1),
    .out2(basic_out2)
  );
  (* bar = 1 *)
  and prim_attr_inst (prim_out, attr_in, attr_in);
  (* baz = 2 *)
  my_checker checker_attr_inst (
    .clk(attr_in),
    .reset(attr_in),
    .c_in1(attr_in),
    .c_in2(attr_in),
    .c_out_comb(checker_out_comb),
    .c_out_ff(checker_out_ff)
  );
  assign attr_out = basic_out1 | basic_out2 | prim_out | checker_out_comb | checker_out_ff;
endmodule
module mod_fixup_target (
  input logic fs_in_target,
  output logic fs_out_target
);
  assign fs_out_target = fs_in_target;
endmodule
module mod_fixup_syntax_user (
  input logic fs_in,
  output wire fs_out
);
  logic fixup_out_val;
  mod_fixup_target fixup_inst (
    .fs_in_target(fs_in),
    .fs_out_target(fixup_out_val)
  );
  assign fs_out = fixup_out_val;
endmodule
module mod_basic_bind (
  input logic in1_bind_def,
  output logic out1_bind_def
);
  assign out1_bind_def = ~in1_bind_def;
endmodule
module mod_bind_container (
  input logic bind_in,
  output wire bind_out
);
  wire basic_out1;
  wire basic_out2;
  wire bind_target_out;
  wire bind_inst_out;
  mod_basic target_inst (
    .in1(bind_in),
    .in2(bind_in),
    .out1(basic_out1),
    .out2(basic_out2)
  );
  mod_basic_bind bind_target_inst (
    .in1_bind_def(bind_in),
    .out1_bind_def(bind_target_out)
  );
  bind mod_basic : target_inst mod_basic_bind bound_inst (
    .in1_bind_def(bind_in),
    .out1_bind_def(bind_inst_out)
  );
  assign bind_out = basic_out1 | basic_out2 | bind_target_out | bind_inst_out;
endmodule
module mod_class_scope (
  input logic cs_in,
  output logic cs_out
);
  class my_class;
    int data;
    function new(int val);
      data = val;
    endfunction
  endclass
  my_class my_obj;
  logic dummy_signal = 0;
  always_ff @(posedge dummy_signal) begin : proc_block_for_class
    my_obj = new(10);
    cs_out = cs_in;
  end
  final begin : final_block_for_class
    my_class another_obj;
    another_obj = new(20);
  end
endmodule
interface my_interface #(parameter int WIDTH = 8) (
  input logic clk,
  output logic [WIDTH-1:0] data
);
  logic [WIDTH-1:0] internal_data;
  modport mp (
    input clk,
    output data
  );
  assign data = internal_data;
endinterface
module mod_virtual_iface (
  input wire v_in,
  output wire v_out
);
  virtual my_interface #(.WIDTH(4)) viface;
  assign v_out = v_in;
endmodule
module mod_iface_user (
  input logic i_clk,
  output logic [7:0] i_data
);
  my_interface #(.WIDTH(8)) iface_inst (.clk(i_clk), .data(i_data));
endmodule
module nested_module (
  input logic nm_in,
  output logic nm_out
);
  assign nm_out = nm_in;
endmodule
package my_package;
  parameter int PKG_PARAM = 5;
endpackage
module mod_package_user (
  input logic pu_in,
  output logic pu_out
);
  nested_module nested_inst (
    .nm_in(pu_in),
    .nm_out(pu_out)
  );
  localparam int LP = my_package::PKG_PARAM;
endmodule
module main_module (
  input wire main_in,
  input wire main_clk,
  input wire main_reset,
  input wire [7:0] main_vec_in,
  inout wire main_bidi1,
  inout wire main_bidi2,
  output wire main_out
);
  wire basic_out1, basic_out2;
  wire arrays_out_large;
  wire [7:0] arrays_out_vec;
  wire implicit_out;
  wire prims_out1, prims_out2, prims_bidi_out, prims_pull_out;
  wire udp_out;
  wire checker_out_comb_named, checker_out_ff_named;
  wire checker_out_comb_ordered, checker_out_ff_ordered;
  wire [1:0] checker_out_comb_array, checker_out_ff_array;
  logic checker_out_comb_proc, checker_out_ff_proc;
  wire uninst_out_inst, uninst_out_uninst;
  wire attr_out;
  wire fixup_out;
  wire bind_out;
  logic class_out;
  wire virtual_iface_out;
  logic [7:0] iface_user_data;
  wire package_user_out;
  mod_basic basic_inst (.in1(main_in), .in2(main_in), .out1(basic_out1), .out2(basic_out2));
  mod_arrays arrays_inst (.in_vec(main_vec_in), .in_large(main_in), .out_vec(arrays_out_vec), .out_large(arrays_out_large));
  mod_implicit implicit_inst (.in_implicit(main_in), .out_implicit(implicit_out));
  mod_prims prims_inst (.p_in1(main_in), .p_in2(main_in), .p_control(main_in), .p_bidi_inout1(main_bidi1), .p_bidi_inout2(main_bidi2), .p_out1(prims_out1), .p_out2(prims_out2), .p_bidi_out(prims_bidi_out), .p_pull_out(prims_pull_out));
  mod_udp udp_inst (.u_in1(main_in), .u_in2(main_in), .u_out(udp_out));
  mod_checker_inst checker_inst (.clk(main_clk), .reset(main_reset), .ch_in1(main_in), .ch_in2(main_in), .ch_out_comb_named(checker_out_comb_named), .ch_out_ff_named(checker_out_ff_named), .ch_out_comb_ordered(checker_out_comb_ordered), .ch_out_ff_ordered(checker_out_ff_ordered), .ch_out_comb_array(checker_out_comb_array), .ch_out_ff_array(checker_out_ff_array), .ch_out_comb_proc(checker_out_comb_proc), .ch_out_ff_proc(checker_out_ff_proc));
  mod_uninstantiated_container uninst_container_inst (.uc_in(main_in), .uc_out_inst(uninst_out_inst), .uc_out_uninst(uninst_out_uninst));
  mod_attributes attributes_inst (.attr_in(main_in), .attr_out(attr_out));
  mod_fixup_syntax_user fixup_inst (.fs_in(main_in), .fs_out(fixup_out));
  mod_bind_container bind_inst (.bind_in(main_in), .bind_out(bind_out));
  mod_class_scope class_inst (.cs_in(main_in), .cs_out(class_out));
  mod_virtual_iface virtual_iface_inst (.v_in(main_in), .v_out(virtual_iface_out));
  mod_iface_user iface_user_inst (.i_clk(main_clk), .i_data(iface_user_data));
  mod_package_user package_user_inst (.pu_in(main_in), .pu_out(package_user_out));
  assign main_out = basic_out1 | basic_out2 | |arrays_out_vec | arrays_out_large | implicit_out | prims_out1 | prims_out2 | prims_bidi_out | prims_pull_out | udp_out | checker_out_comb_named | checker_out_ff_named | checker_out_comb_ordered | checker_out_ff_ordered | |checker_out_comb_array | |checker_out_ff_array | checker_out_comb_proc | checker_out_ff_proc | uninst_out_inst | uninst_out_uninst | attr_out | fixup_out | bind_out | class_out | virtual_iface_out | |iface_user_data | package_user_out;
endmodule

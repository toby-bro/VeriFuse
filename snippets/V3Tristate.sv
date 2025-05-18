module TristateBasic(
    input wire en,
    input wire data,
    inout wire tri_io,
    output wire out
);
    assign tri_io = en ? data : 1'bz;
    assign out = tri_io;
endmodule
module BufIfGate(
    input wire data_in,
    input wire enable_in,
    output wire out_bufif
);
    bufif1 b1 (out_bufif, data_in, enable_in);
endmodule
module PullUpDown(
    input wire data_in,
    output wire out_pull,
    inout wire tri_pulled
);
    pullup (tri_pulled);
    assign out_pull = tri_pulled;
endmodule
module WiredNet(
    input wire data1,
    input wire data2,
    output wire out_wired
);
    wor w_or;
    assign w_or = data1;
    assign w_or = data2;
    assign out_wired = w_or;
endmodule
module StrengthAssign(
    input wire data_h,
    input wire data_l,
    output wire out_strength
);
    tri strength_wire;
    assign (pull1, pull0) strength_wire = data_h;
    assign (weak1, weak0) strength_wire = data_l;
    assign out_strength = strength_wire;
endmodule
module CaseEq(
    inout wire [3:0] data_io,
    output wire match_z_eq,
    output wire match_x_neq
);
    assign match_z_eq = (data_io === 4'b101z);
    assign match_x_neq = (data_io !== 4'b1x0x);
endmodule
module SelectSlice(
    input wire [7:0] data_in,
    input wire sel_en,
    output wire [3:0] out_slice,
    output wire out_bit
);
    wire [7:0] tri_bus;
    assign tri_bus = sel_en ? data_in : 8'bz;
    assign out_slice = tri_bus[3:0];
    assign out_bit = tri_bus[7];
endmodule
module ConcatTri(
    input wire a,
    input wire [2:0] b,
    input wire c_en,
    output wire [4:0] out_concat
);
    wire c_tri;
    assign c_tri = c_en ? 1'b1 : 1'bz;
    assign out_concat = {a, b, c_tri};
endmodule
module LogicTri(
    input wire a_in,
    input wire b_en,
    output wire or_out,
    output wire and_out
);
    wire b_tri;
    assign b_tri = b_en ? 1'b1 : 1'bz;
    assign or_out = a_in | b_tri;
    assign and_out = a_in & b_tri;
endmodule
module CountBitsTri(
    input wire [7:0] data_in,
    input wire en_tri,
    output wire [3:0] count_ones,
    output wire [3:0] count_z_ph,
    output wire [3:0] count_0s_ph
);
    wire [7:0] tri_data;
    assign tri_data = en_tri ? 8'b1011_z00z : data_in;
    assign count_ones = $countones(tri_data);
    assign count_z_ph = 4'b0000;
    assign count_0s_ph = tri_data[3:0];
endmodule
module CaseZExample(
    input wire [1:0] sel,
    input wire [3:0] data_in,
    output reg [3:0] case_out
);
    wire [3:0] local_data;
    assign local_data = data_in;
    always @* begin
        casez (sel)
            2'b0?: case_out = local_data;
            2'b10: case_out = 4'b1111;
            default: case_out = 4'b0000;
        endcase
    end
endmodule
module TernaryTri(
    input wire sel_cond,
    input wire data_then,
    input wire data_else_en,
    output wire out_ternary
);
    wire data_else_tri;
    assign data_else_tri = data_else_en ? 1'b0 : 1'bz;
    assign out_ternary = sel_cond ? data_then : data_else_tri;
endmodule
module MultipleDrivers(
    input wire in1,
    input wire in2,
    input wire in3,
    output wire out_multi
);
    wire multi_driver_wire;
    assign multi_driver_wire = in1;
    assign multi_driver_wire = in2;
    assign multi_driver_wire = in3;
    assign out_multi = multi_driver_wire;
endmodule
module AssignmentVariations(
    input wire [7:0] data_in,
    input wire en,
    output wire [7:0] out_assign_z
);
    wire [7:0] z_wire;
    assign z_wire = data_in;
    assign z_wire = en ? 8'bz : data_in;
    assign out_assign_z = z_wire;
endmodule

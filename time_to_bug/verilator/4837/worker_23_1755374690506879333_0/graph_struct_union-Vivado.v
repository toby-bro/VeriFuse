// Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
// Copyright 2022-2023 Advanced Micro Devices, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2023.2.1 (lin64) Build 4081461 Thu Dec 14 12:22:04 MST 2023
// Date        : Sat Aug 16 13:07:20 2025
// Host        : a9 running 64-bit Ubuntu 24.04.2 LTS
// Command     : write_verilog dist/worker_23_1755374690506879333_0/graph_struct_union-Vivado.v
// Design      : graph_struct_union
// Purpose     : This is a Verilog netlist of the current design or from a specific cell of the design. The output is an
//               IEEE 1364-2001 compliant Verilog HDL file that contains netlist information obtained from the input
//               design files.
// Device      : xc7vx485tffg1157-1
// --------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* STRUCTURAL_NETLIST = "yes" *)
module graph_struct_union
   (bus_in,
    clk,
    inj_data_in_1755374690838_411,
    inj_en_1755374690838_231,
    inj_packed_in_1755374690832_418,
    rst,
    bus_out,
    inj_data_out_1755374690838_314,
    inj_field0_byte_o_1755374690832_197);
  input [31:0]bus_in;
  input clk;
  input [7:0]inj_data_in_1755374690838_411;
  input inj_en_1755374690838_231;
  input [15:0]inj_packed_in_1755374690832_418;
  input rst;
  output [31:0]bus_out;
  output [7:0]inj_data_out_1755374690838_314;
  output [7:0]inj_field0_byte_o_1755374690832_197;

  wire \<const0> ;
  wire [31:0]bus_in;
  wire [31:0]bus_out;
  wire [31:0]bus_out_OBUF;
  wire clk;
  wire clk_IBUF;
  wire clk_IBUF_BUFG;
  wire [7:0]inj_data_in_1755374690838_411;
  wire [7:0]inj_data_in_1755374690838_411_IBUF;
  wire [7:0]inj_data_out_1755374690838_314;
  wire [7:0]inj_data_out_1755374690838_314_OBUF;
  wire inj_en_1755374690838_231;
  wire inj_en_1755374690838_231_IBUF;
  wire [7:0]inj_field0_byte_o_1755374690832_197;
  wire [7:0]inj_field0_byte_o_1755374690832_197_OBUF;
  wire [15:0]inj_packed_in_1755374690832_418;

  GND GND
       (.G(\<const0> ));
  IBUF \bus_in_IBUF[0]_inst 
       (.I(bus_in[0]),
        .O(bus_out_OBUF[24]));
  IBUF \bus_in_IBUF[10]_inst 
       (.I(bus_in[10]),
        .O(bus_out_OBUF[18]));
  IBUF \bus_in_IBUF[11]_inst 
       (.I(bus_in[11]),
        .O(bus_out_OBUF[19]));
  IBUF \bus_in_IBUF[12]_inst 
       (.I(bus_in[12]),
        .O(bus_out_OBUF[20]));
  IBUF \bus_in_IBUF[13]_inst 
       (.I(bus_in[13]),
        .O(bus_out_OBUF[21]));
  IBUF \bus_in_IBUF[14]_inst 
       (.I(bus_in[14]),
        .O(bus_out_OBUF[22]));
  IBUF \bus_in_IBUF[15]_inst 
       (.I(bus_in[15]),
        .O(bus_out_OBUF[23]));
  IBUF \bus_in_IBUF[16]_inst 
       (.I(bus_in[16]),
        .O(bus_out_OBUF[8]));
  IBUF \bus_in_IBUF[17]_inst 
       (.I(bus_in[17]),
        .O(bus_out_OBUF[9]));
  IBUF \bus_in_IBUF[18]_inst 
       (.I(bus_in[18]),
        .O(bus_out_OBUF[10]));
  IBUF \bus_in_IBUF[19]_inst 
       (.I(bus_in[19]),
        .O(bus_out_OBUF[11]));
  IBUF \bus_in_IBUF[1]_inst 
       (.I(bus_in[1]),
        .O(bus_out_OBUF[25]));
  IBUF \bus_in_IBUF[20]_inst 
       (.I(bus_in[20]),
        .O(bus_out_OBUF[12]));
  IBUF \bus_in_IBUF[21]_inst 
       (.I(bus_in[21]),
        .O(bus_out_OBUF[13]));
  IBUF \bus_in_IBUF[22]_inst 
       (.I(bus_in[22]),
        .O(bus_out_OBUF[14]));
  IBUF \bus_in_IBUF[23]_inst 
       (.I(bus_in[23]),
        .O(bus_out_OBUF[15]));
  IBUF \bus_in_IBUF[24]_inst 
       (.I(bus_in[24]),
        .O(bus_out_OBUF[0]));
  IBUF \bus_in_IBUF[25]_inst 
       (.I(bus_in[25]),
        .O(bus_out_OBUF[1]));
  IBUF \bus_in_IBUF[26]_inst 
       (.I(bus_in[26]),
        .O(bus_out_OBUF[2]));
  IBUF \bus_in_IBUF[27]_inst 
       (.I(bus_in[27]),
        .O(bus_out_OBUF[3]));
  IBUF \bus_in_IBUF[28]_inst 
       (.I(bus_in[28]),
        .O(bus_out_OBUF[4]));
  IBUF \bus_in_IBUF[29]_inst 
       (.I(bus_in[29]),
        .O(bus_out_OBUF[5]));
  IBUF \bus_in_IBUF[2]_inst 
       (.I(bus_in[2]),
        .O(bus_out_OBUF[26]));
  IBUF \bus_in_IBUF[30]_inst 
       (.I(bus_in[30]),
        .O(bus_out_OBUF[6]));
  IBUF \bus_in_IBUF[31]_inst 
       (.I(bus_in[31]),
        .O(bus_out_OBUF[7]));
  IBUF \bus_in_IBUF[3]_inst 
       (.I(bus_in[3]),
        .O(bus_out_OBUF[27]));
  IBUF \bus_in_IBUF[4]_inst 
       (.I(bus_in[4]),
        .O(bus_out_OBUF[28]));
  IBUF \bus_in_IBUF[5]_inst 
       (.I(bus_in[5]),
        .O(bus_out_OBUF[29]));
  IBUF \bus_in_IBUF[6]_inst 
       (.I(bus_in[6]),
        .O(bus_out_OBUF[30]));
  IBUF \bus_in_IBUF[7]_inst 
       (.I(bus_in[7]),
        .O(bus_out_OBUF[31]));
  IBUF \bus_in_IBUF[8]_inst 
       (.I(bus_in[8]),
        .O(bus_out_OBUF[16]));
  IBUF \bus_in_IBUF[9]_inst 
       (.I(bus_in[9]),
        .O(bus_out_OBUF[17]));
  OBUF \bus_out_OBUF[0]_inst 
       (.I(bus_out_OBUF[0]),
        .O(bus_out[0]));
  OBUF \bus_out_OBUF[10]_inst 
       (.I(bus_out_OBUF[10]),
        .O(bus_out[10]));
  OBUF \bus_out_OBUF[11]_inst 
       (.I(bus_out_OBUF[11]),
        .O(bus_out[11]));
  OBUF \bus_out_OBUF[12]_inst 
       (.I(bus_out_OBUF[12]),
        .O(bus_out[12]));
  OBUF \bus_out_OBUF[13]_inst 
       (.I(bus_out_OBUF[13]),
        .O(bus_out[13]));
  OBUF \bus_out_OBUF[14]_inst 
       (.I(bus_out_OBUF[14]),
        .O(bus_out[14]));
  OBUF \bus_out_OBUF[15]_inst 
       (.I(bus_out_OBUF[15]),
        .O(bus_out[15]));
  OBUF \bus_out_OBUF[16]_inst 
       (.I(bus_out_OBUF[16]),
        .O(bus_out[16]));
  OBUF \bus_out_OBUF[17]_inst 
       (.I(bus_out_OBUF[17]),
        .O(bus_out[17]));
  OBUF \bus_out_OBUF[18]_inst 
       (.I(bus_out_OBUF[18]),
        .O(bus_out[18]));
  OBUF \bus_out_OBUF[19]_inst 
       (.I(bus_out_OBUF[19]),
        .O(bus_out[19]));
  OBUF \bus_out_OBUF[1]_inst 
       (.I(bus_out_OBUF[1]),
        .O(bus_out[1]));
  OBUF \bus_out_OBUF[20]_inst 
       (.I(bus_out_OBUF[20]),
        .O(bus_out[20]));
  OBUF \bus_out_OBUF[21]_inst 
       (.I(bus_out_OBUF[21]),
        .O(bus_out[21]));
  OBUF \bus_out_OBUF[22]_inst 
       (.I(bus_out_OBUF[22]),
        .O(bus_out[22]));
  OBUF \bus_out_OBUF[23]_inst 
       (.I(bus_out_OBUF[23]),
        .O(bus_out[23]));
  OBUF \bus_out_OBUF[24]_inst 
       (.I(bus_out_OBUF[24]),
        .O(bus_out[24]));
  OBUF \bus_out_OBUF[25]_inst 
       (.I(bus_out_OBUF[25]),
        .O(bus_out[25]));
  OBUF \bus_out_OBUF[26]_inst 
       (.I(bus_out_OBUF[26]),
        .O(bus_out[26]));
  OBUF \bus_out_OBUF[27]_inst 
       (.I(bus_out_OBUF[27]),
        .O(bus_out[27]));
  OBUF \bus_out_OBUF[28]_inst 
       (.I(bus_out_OBUF[28]),
        .O(bus_out[28]));
  OBUF \bus_out_OBUF[29]_inst 
       (.I(bus_out_OBUF[29]),
        .O(bus_out[29]));
  OBUF \bus_out_OBUF[2]_inst 
       (.I(bus_out_OBUF[2]),
        .O(bus_out[2]));
  OBUF \bus_out_OBUF[30]_inst 
       (.I(bus_out_OBUF[30]),
        .O(bus_out[30]));
  OBUF \bus_out_OBUF[31]_inst 
       (.I(bus_out_OBUF[31]),
        .O(bus_out[31]));
  OBUF \bus_out_OBUF[3]_inst 
       (.I(bus_out_OBUF[3]),
        .O(bus_out[3]));
  OBUF \bus_out_OBUF[4]_inst 
       (.I(bus_out_OBUF[4]),
        .O(bus_out[4]));
  OBUF \bus_out_OBUF[5]_inst 
       (.I(bus_out_OBUF[5]),
        .O(bus_out[5]));
  OBUF \bus_out_OBUF[6]_inst 
       (.I(bus_out_OBUF[6]),
        .O(bus_out[6]));
  OBUF \bus_out_OBUF[7]_inst 
       (.I(bus_out_OBUF[7]),
        .O(bus_out[7]));
  OBUF \bus_out_OBUF[8]_inst 
       (.I(bus_out_OBUF[8]),
        .O(bus_out[8]));
  OBUF \bus_out_OBUF[9]_inst 
       (.I(bus_out_OBUF[9]),
        .O(bus_out[9]));
  BUFG clk_IBUF_BUFG_inst
       (.I(clk_IBUF),
        .O(clk_IBUF_BUFG));
  IBUF clk_IBUF_inst
       (.I(clk),
        .O(clk_IBUF));
  IBUF \inj_data_in_1755374690838_411_IBUF[0]_inst 
       (.I(inj_data_in_1755374690838_411[0]),
        .O(inj_data_in_1755374690838_411_IBUF[0]));
  IBUF \inj_data_in_1755374690838_411_IBUF[1]_inst 
       (.I(inj_data_in_1755374690838_411[1]),
        .O(inj_data_in_1755374690838_411_IBUF[1]));
  IBUF \inj_data_in_1755374690838_411_IBUF[2]_inst 
       (.I(inj_data_in_1755374690838_411[2]),
        .O(inj_data_in_1755374690838_411_IBUF[2]));
  IBUF \inj_data_in_1755374690838_411_IBUF[3]_inst 
       (.I(inj_data_in_1755374690838_411[3]),
        .O(inj_data_in_1755374690838_411_IBUF[3]));
  IBUF \inj_data_in_1755374690838_411_IBUF[4]_inst 
       (.I(inj_data_in_1755374690838_411[4]),
        .O(inj_data_in_1755374690838_411_IBUF[4]));
  IBUF \inj_data_in_1755374690838_411_IBUF[5]_inst 
       (.I(inj_data_in_1755374690838_411[5]),
        .O(inj_data_in_1755374690838_411_IBUF[5]));
  IBUF \inj_data_in_1755374690838_411_IBUF[6]_inst 
       (.I(inj_data_in_1755374690838_411[6]),
        .O(inj_data_in_1755374690838_411_IBUF[6]));
  IBUF \inj_data_in_1755374690838_411_IBUF[7]_inst 
       (.I(inj_data_in_1755374690838_411[7]),
        .O(inj_data_in_1755374690838_411_IBUF[7]));
  OBUF \inj_data_out_1755374690838_314_OBUF[0]_inst 
       (.I(inj_data_out_1755374690838_314_OBUF[0]),
        .O(inj_data_out_1755374690838_314[0]));
  OBUF \inj_data_out_1755374690838_314_OBUF[1]_inst 
       (.I(inj_data_out_1755374690838_314_OBUF[1]),
        .O(inj_data_out_1755374690838_314[1]));
  OBUF \inj_data_out_1755374690838_314_OBUF[2]_inst 
       (.I(inj_data_out_1755374690838_314_OBUF[2]),
        .O(inj_data_out_1755374690838_314[2]));
  OBUF \inj_data_out_1755374690838_314_OBUF[3]_inst 
       (.I(inj_data_out_1755374690838_314_OBUF[3]),
        .O(inj_data_out_1755374690838_314[3]));
  OBUF \inj_data_out_1755374690838_314_OBUF[4]_inst 
       (.I(inj_data_out_1755374690838_314_OBUF[4]),
        .O(inj_data_out_1755374690838_314[4]));
  OBUF \inj_data_out_1755374690838_314_OBUF[5]_inst 
       (.I(inj_data_out_1755374690838_314_OBUF[5]),
        .O(inj_data_out_1755374690838_314[5]));
  OBUF \inj_data_out_1755374690838_314_OBUF[6]_inst 
       (.I(inj_data_out_1755374690838_314_OBUF[6]),
        .O(inj_data_out_1755374690838_314[6]));
  OBUF \inj_data_out_1755374690838_314_OBUF[7]_inst 
       (.I(inj_data_out_1755374690838_314_OBUF[7]),
        .O(inj_data_out_1755374690838_314[7]));
  FDRE \inj_data_out_1755374690838_314_reg[0] 
       (.C(clk_IBUF_BUFG),
        .CE(inj_en_1755374690838_231_IBUF),
        .D(inj_data_in_1755374690838_411_IBUF[0]),
        .Q(inj_data_out_1755374690838_314_OBUF[0]),
        .R(\<const0> ));
  FDRE \inj_data_out_1755374690838_314_reg[1] 
       (.C(clk_IBUF_BUFG),
        .CE(inj_en_1755374690838_231_IBUF),
        .D(inj_data_in_1755374690838_411_IBUF[1]),
        .Q(inj_data_out_1755374690838_314_OBUF[1]),
        .R(\<const0> ));
  FDRE \inj_data_out_1755374690838_314_reg[2] 
       (.C(clk_IBUF_BUFG),
        .CE(inj_en_1755374690838_231_IBUF),
        .D(inj_data_in_1755374690838_411_IBUF[2]),
        .Q(inj_data_out_1755374690838_314_OBUF[2]),
        .R(\<const0> ));
  FDRE \inj_data_out_1755374690838_314_reg[3] 
       (.C(clk_IBUF_BUFG),
        .CE(inj_en_1755374690838_231_IBUF),
        .D(inj_data_in_1755374690838_411_IBUF[3]),
        .Q(inj_data_out_1755374690838_314_OBUF[3]),
        .R(\<const0> ));
  FDRE \inj_data_out_1755374690838_314_reg[4] 
       (.C(clk_IBUF_BUFG),
        .CE(inj_en_1755374690838_231_IBUF),
        .D(inj_data_in_1755374690838_411_IBUF[4]),
        .Q(inj_data_out_1755374690838_314_OBUF[4]),
        .R(\<const0> ));
  FDRE \inj_data_out_1755374690838_314_reg[5] 
       (.C(clk_IBUF_BUFG),
        .CE(inj_en_1755374690838_231_IBUF),
        .D(inj_data_in_1755374690838_411_IBUF[5]),
        .Q(inj_data_out_1755374690838_314_OBUF[5]),
        .R(\<const0> ));
  FDRE \inj_data_out_1755374690838_314_reg[6] 
       (.C(clk_IBUF_BUFG),
        .CE(inj_en_1755374690838_231_IBUF),
        .D(inj_data_in_1755374690838_411_IBUF[6]),
        .Q(inj_data_out_1755374690838_314_OBUF[6]),
        .R(\<const0> ));
  FDRE \inj_data_out_1755374690838_314_reg[7] 
       (.C(clk_IBUF_BUFG),
        .CE(inj_en_1755374690838_231_IBUF),
        .D(inj_data_in_1755374690838_411_IBUF[7]),
        .Q(inj_data_out_1755374690838_314_OBUF[7]),
        .R(\<const0> ));
  IBUF inj_en_1755374690838_231_IBUF_inst
       (.I(inj_en_1755374690838_231),
        .O(inj_en_1755374690838_231_IBUF));
  OBUF \inj_field0_byte_o_1755374690832_197_OBUF[0]_inst 
       (.I(inj_field0_byte_o_1755374690832_197_OBUF[0]),
        .O(inj_field0_byte_o_1755374690832_197[0]));
  OBUF \inj_field0_byte_o_1755374690832_197_OBUF[1]_inst 
       (.I(inj_field0_byte_o_1755374690832_197_OBUF[1]),
        .O(inj_field0_byte_o_1755374690832_197[1]));
  OBUF \inj_field0_byte_o_1755374690832_197_OBUF[2]_inst 
       (.I(inj_field0_byte_o_1755374690832_197_OBUF[2]),
        .O(inj_field0_byte_o_1755374690832_197[2]));
  OBUF \inj_field0_byte_o_1755374690832_197_OBUF[3]_inst 
       (.I(inj_field0_byte_o_1755374690832_197_OBUF[3]),
        .O(inj_field0_byte_o_1755374690832_197[3]));
  OBUF \inj_field0_byte_o_1755374690832_197_OBUF[4]_inst 
       (.I(inj_field0_byte_o_1755374690832_197_OBUF[4]),
        .O(inj_field0_byte_o_1755374690832_197[4]));
  OBUF \inj_field0_byte_o_1755374690832_197_OBUF[5]_inst 
       (.I(inj_field0_byte_o_1755374690832_197_OBUF[5]),
        .O(inj_field0_byte_o_1755374690832_197[5]));
  OBUF \inj_field0_byte_o_1755374690832_197_OBUF[6]_inst 
       (.I(inj_field0_byte_o_1755374690832_197_OBUF[6]),
        .O(inj_field0_byte_o_1755374690832_197[6]));
  OBUF \inj_field0_byte_o_1755374690832_197_OBUF[7]_inst 
       (.I(inj_field0_byte_o_1755374690832_197_OBUF[7]),
        .O(inj_field0_byte_o_1755374690832_197[7]));
  IBUF \inj_packed_in_1755374690832_418_IBUF[0]_inst 
       (.I(inj_packed_in_1755374690832_418[0]),
        .O(inj_field0_byte_o_1755374690832_197_OBUF[0]));
  IBUF \inj_packed_in_1755374690832_418_IBUF[1]_inst 
       (.I(inj_packed_in_1755374690832_418[1]),
        .O(inj_field0_byte_o_1755374690832_197_OBUF[1]));
  IBUF \inj_packed_in_1755374690832_418_IBUF[2]_inst 
       (.I(inj_packed_in_1755374690832_418[2]),
        .O(inj_field0_byte_o_1755374690832_197_OBUF[2]));
  IBUF \inj_packed_in_1755374690832_418_IBUF[3]_inst 
       (.I(inj_packed_in_1755374690832_418[3]),
        .O(inj_field0_byte_o_1755374690832_197_OBUF[3]));
  IBUF \inj_packed_in_1755374690832_418_IBUF[4]_inst 
       (.I(inj_packed_in_1755374690832_418[4]),
        .O(inj_field0_byte_o_1755374690832_197_OBUF[4]));
  IBUF \inj_packed_in_1755374690832_418_IBUF[5]_inst 
       (.I(inj_packed_in_1755374690832_418[5]),
        .O(inj_field0_byte_o_1755374690832_197_OBUF[5]));
  IBUF \inj_packed_in_1755374690832_418_IBUF[6]_inst 
       (.I(inj_packed_in_1755374690832_418[6]),
        .O(inj_field0_byte_o_1755374690832_197_OBUF[6]));
  IBUF \inj_packed_in_1755374690832_418_IBUF[7]_inst 
       (.I(inj_packed_in_1755374690832_418[7]),
        .O(inj_field0_byte_o_1755374690832_197_OBUF[7]));
endmodule

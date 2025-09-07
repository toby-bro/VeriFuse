module ImplicitTimeScaleModule (
    input logic in_its,
    output logic out_its
);
    assign out_its = in_its;
endmodule

module ModCompareVec (
    input logic [3:0] v1,
    input logic [3:0] v2,
    output logic eq
);
    assign eq = (v1 == v2);
endmodule

module multi_port_decl_module (
    input logic [3:0] p_a,
    input logic [3:0] p_b,
    input logic single_in,
    output logic single_out
);
    always_comb begin
        single_out = single_in;
    end
endmodule

module split_inputs_outputs_only (
    input logic [7:0] in_val_a_l,
    input logic [7:0] in_val_b_l,
    output logic [8:0] out_val_c_l,
    output logic [7:0] out_val_d_l
);
    always @(*) begin
        out_val_c_l = in_val_a_l + in_val_b_l;
        out_val_d_l = in_val_a_l - in_val_b_l;
    end
endmodule

module packed_union_module (
    input wire clk,
    input logic [15:0] in_data,
    input bit inj_in_bit_1755356032427_491,
    input logic inj_in_its_1755356032428_511,
    input logic inj_in_q_1755356032435_222,
    input logic [7:0] inj_in_val_a_l_1755356032565_367,
    input logic [7:0] inj_in_val_b_l_1755356032565_172,
    input logic [3:0] inj_p_a_1755356032531_261,
    input logic [3:0] inj_p_b_1755356032531_46,
    input wire rst,
    output logic [7:0] inj_byte_out_1755356032582_782,
    output logic inj_eq_1755356032546_266,
    output logic inj_out_data_pull0_1755356032685_599,
    output logic inj_out_data_pull1_1755356032685_132,
    output logic inj_out_its_1755356032428_603,
    output logic inj_out_logic_1755356032427_789,
    output logic inj_out_r_1755356032435_154,
    output logic [8:0] inj_out_val_c_l_1755356032565_753,
    output logic [7:0] inj_out_val_d_l_1755356032565_633,
    output logic [15:0] inj_packed_out_1755356032583_802,
    output logic inj_single_out_1755356032531_463,
    output logic [15:0] out_data
);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } bytes_s;
    typedef union packed {
        logic  [15:0] whole;
        bytes_s       bytes;
    } data_u;
    data_u mydata;
    // BEGIN: PackedStructOps_ts1755356032583
    typedef struct packed {
        logic [7:0] low_ts1755356032583;
        logic [7:0] high_ts1755356032583;
    } pair_t;
    pair_t data_pair;
    // BEGIN: module_with_unconnected_drive_ts1755356032685
    assign inj_out_data_pull1_1755356032685_132 = inj_in_q_1755356032435_222;
    assign inj_out_data_pull0_1755356032685_599 = ~inj_in_q_1755356032435_222;
    // END: module_with_unconnected_drive_ts1755356032685

    assign data_pair.high_ts1755356032583 = in_data[15:8];
    assign data_pair.low_ts1755356032583 = inj_in_val_a_l_1755356032565_367;
    assign inj_byte_out_1755356032582_782 = data_pair.high_ts1755356032583;
    assign inj_packed_out_1755356032583_802[15:8] = data_pair.high_ts1755356032583;
    assign inj_packed_out_1755356032583_802[7:0] = data_pair.low_ts1755356032583 + inj_in_val_a_l_1755356032565_367;
    // END: PackedStructOps_ts1755356032583

    split_inputs_outputs_only split_inputs_outputs_only_inst_1755356032565_7975 (
        .in_val_a_l(inj_in_val_a_l_1755356032565_367),
        .in_val_b_l(inj_in_val_b_l_1755356032565_172),
        .out_val_c_l(inj_out_val_c_l_1755356032565_753),
        .out_val_d_l(inj_out_val_d_l_1755356032565_633)
    );
    ModCompareVec ModCompareVec_inst_1755356032546_5936 (
        .v2(inj_p_b_1755356032531_46),
        .eq(inj_eq_1755356032546_266),
        .v1(inj_p_a_1755356032531_261)
    );
    multi_port_decl_module multi_port_decl_module_inst_1755356032531_1418 (
        .p_a(inj_p_a_1755356032531_261),
        .p_b(inj_p_b_1755356032531_46),
        .single_in(inj_in_its_1755356032428_511),
        .single_out(inj_single_out_1755356032531_463)
    );
    // BEGIN: LintSensitiveList_ts1755356032440
    always_comb begin
        inj_out_r_1755356032435_154 = inj_in_its_1755356032428_511 | inj_in_q_1755356032435_222;
    end
    // END: LintSensitiveList_ts1755356032440

    ImplicitTimeScaleModule ImplicitTimeScaleModule_inst_1755356032428_9408 (
        .out_its(inj_out_its_1755356032428_603),
        .in_its(inj_in_its_1755356032428_511)
    );
    // BEGIN: DummyHierModule_ts1755356032427
    assign inj_out_logic_1755356032427_789 = inj_in_bit_1755356032427_491;
    // END: DummyHierModule_ts1755356032427

    always_comb begin
        mydata.whole = in_data;
        if (mydata.bytes.hi[7])
            out_data = {8'h00, mydata.bytes.lo};
        else
            out_data = {8'h00, mydata.bytes.hi};
    end
endmodule


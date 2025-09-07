module nested_blocks (
    input logic data_value,
    input logic level1_en,
    input logic level2_en,
    output logic result_out
);
    always_comb begin : main_block 
        result_out = 1'b0; 
        if (level1_en) begin : inner_block1 
            if (level2_en) begin : inner_block2 
                result_out = data_value;
            end 
        end 
    end
endmodule

module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [3:0] inj_a_1755301683265_754,
    input logic [3:0] inj_b_1755301683265_298,
    input logic inj_data_value_1755301683149_555,
    input logic [7:0] inj_in_false_d_1755301683159_692,
    input int inj_in_port_1755301683145_593,
    input logic [7:0] inj_in_true_d_1755301683159_497,
    input logic inj_level1_en_1755301683149_533,
    input logic inj_level2_en_1755301683149_657,
    input wire rst,
    output logic [31:0] bus_out,
    output logic [15:0] inj_out_concat_1755301683265_998,
    output int inj_out_port_1755301683145_366,
    output logic [7:0] inj_out_reg_d_1755301683159_117,
    output int inj_out_val_1755301683195_143,
    output logic inj_result_out_1755301683149_237
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } bytes_t;
    typedef union packed {
        logic  [31:0] word;
        bytes_t       bytes;
    } data_u;
    data_u din, dout;
    // BEGIN: ConcatVectorOps_ts1755301683265
    assign inj_out_concat_1755301683265_998 = {inj_a_1755301683265_754, inj_b_1755301683265_298, inj_in_false_d_1755301683159_692};
    // END: ConcatVectorOps_ts1755301683265

    // BEGIN: system_names_mod_ts1755301683195
    assign inj_out_val_1755301683195_143 = $bits(inj_in_port_1755301683145_593);
    // END: system_names_mod_ts1755301683195

    // BEGIN: split_conditional_nb_ts1755301683159
    always @(posedge clk) begin
        if (inj_level2_en_1755301683149_657) begin
            inj_out_reg_d_1755301683159_117 <= inj_in_true_d_1755301683159_497;
        end else begin
            inj_out_reg_d_1755301683159_117 <= inj_in_false_d_1755301683159_692;
        end
    end
    // END: split_conditional_nb_ts1755301683159

    nested_blocks nested_blocks_inst_1755301683149_2222 (
        .level2_en(inj_level2_en_1755301683149_657),
        .result_out(inj_result_out_1755301683149_237),
        .data_value(inj_data_value_1755301683149_555),
        .level1_en(inj_level1_en_1755301683149_533)
    );
    // BEGIN: Module_IfNoneParam_ts1755301683145
    assign inj_out_port_1755301683145_366 = inj_in_port_1755301683145_593;
    // END: Module_IfNoneParam_ts1755301683145

    always_comb begin
        din.word         = bus_in;
        dout.word        = 32'h0;
        dout.bytes.byte0 = din.bytes.byte3;
        dout.bytes.byte1 = din.bytes.byte2;
        dout.bytes.byte2 = din.bytes.byte1;
        dout.bytes.byte3 = din.bytes.byte0;
    end
    assign bus_out = dout.word;
endmodule


module FunctionTaskMod (
    input logic [7:0] data_in,
    output logic is_even
);
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp;
        tmp = v;
    endtask
    assign is_even = check_even(data_in);
endmodule

module graph_struct_union (
    input logic [31:0] bus_in,
    input wire clk,
    input logic [7:0] inj_in1_1755301683136_381,
    input logic [7:0] inj_in2_1755301683136_197,
    input logic inj_in_data_1755301683231_169,
    input wire rst,
    output logic [31:0] bus_out,
    output logic inj_is_even_1755301683175_628,
    output logic [7:0] inj_out1_1755301683136_398,
    output logic [7:0] inj_out2_1755301683136_95,
    output logic inj_out_a_1755301683279_291,
    output logic inj_out_data_pull0_1755301683231_603,
    output logic inj_out_data_pull1_1755301683231_704,
    output logic [3:0] inj_out_h_1755301683381_485,
    output logic [3:0] inj_out_l_1755301683381_230
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
    // BEGIN: ModuleComb_ts1755301683136
    logic [7:0] internal_wire_ts1755301683136;
    // BEGIN: mod_name_conflict_ts1755301683279
    logic conflict_var_ts1755301683279;
    parameter int conflict_param = 1;
    // BEGIN: concat_assign_ts1755301683381
    assign {inj_out_h_1755301683381_485, inj_out_l_1755301683381_230} = inj_in1_1755301683136_381;
    // END: concat_assign_ts1755301683381

    assign inj_out_a_1755301683279_291 = inj_in_data_1755301683231_169;
    // END: mod_name_conflict_ts1755301683279

    // BEGIN: module_with_unconnected_drive_ts1755301683231
    assign inj_out_data_pull1_1755301683231_704 = inj_in_data_1755301683231_169;
    assign inj_out_data_pull0_1755301683231_603 = ~inj_in_data_1755301683231_169;
    // END: module_with_unconnected_drive_ts1755301683231

    FunctionTaskMod FunctionTaskMod_inst_1755301683175_133 (
        .is_even(inj_is_even_1755301683175_628),
        .data_in(inj_in1_1755301683136_381)
    );
    assign internal_wire_ts1755301683136 = inj_in1_1755301683136_381 + inj_in2_1755301683136_197;
    always_comb begin
        if (internal_wire_ts1755301683136 > 8'd128) begin
            inj_out1_1755301683136_398 = internal_wire_ts1755301683136 - 1;
        end else begin
            inj_out1_1755301683136_398 = internal_wire_ts1755301683136 + 1;
        end
        inj_out2_1755301683136_95 = internal_wire_ts1755301683136 / 2;
    end
    // END: ModuleComb_ts1755301683136

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


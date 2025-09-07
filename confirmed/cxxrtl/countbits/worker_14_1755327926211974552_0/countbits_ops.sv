interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module BitwiseOperations (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic [7:0] result_and,
    output logic [7:0] result_or,
    output logic [7:0] result_xor
);
    assign result_and = a & b;
    assign result_or = a | c;
    assign result_xor = b ^ c;
endmodule

module basic_assign_if (
    input logic in_a,
    input logic in_b,
    output logic out_c
);
    logic intermediate_wire;
    assign intermediate_wire = in_a & in_b;
    always_comb begin
        if (intermediate_wire) begin
            out_c = 1'b1;
        end else begin
            out_c = 1'b0;
        end
    end
endmodule

module mod_name_conflict (
    input logic in_a,
    output logic out_a
);
    logic conflict_var;
    parameter int conflict_param = 1;
    assign out_a = in_a;
endmodule

module module_sequential_writes (
    input logic [7:0] addr,
    input logic [7:0] wdata,
    output logic write_status
);
    my_if vif_bus();
    always_comb begin
        vif_bus.data = wdata;
        vif_bus.ready = 1'b1;
        vif_bus.valid = 1'b0;
        write_status = vif_bus.ready;
    end
endmodule

module split_mixed_cond_seq (
    input logic clk_e,
    input logic condition_e,
    input logic [7:0] in_override_e,
    input logic [7:0] in_val_e,
    output logic [7:0] out_val_e,
    output logic status_e
);
    logic [7:0] temp_val_e;
    always @(posedge clk_e) begin
        temp_val_e <= in_val_e + 5;
        if (condition_e) begin
            out_val_e <= temp_val_e;
            status_e <= 1;
        end else begin
            out_val_e <= in_override_e;
            status_e <= 0;
        end
    end
endmodule

module unsupported_cond_expr (
    input bit condition_m10,
    input logic [7:0] in_val_m10,
    output logic [7:0] out_val_m10
);
    logic [7:0] var_m10;
    always_comb begin
        var_m10 = in_val_m10;
        out_val_m10 = condition_m10 ? var_m10 : var_m10;
        var_m10++;
    end
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic [7:0] inj_c_1755327926877_515,
    input bit inj_condition_m10_1755327926899_772,
    input logic inj_in_a_1755327926597_456,
    input logic inj_in_b_1755327926597_288,
    input int inj_in_val_1755327926679_968,
    input logic [1:0] inj_in_val_1755327927134_292,
    input logic [7:0] inj_wdata_1755327926605_780,
    input wire [63:0] inj_wide_a_1755327927347_668,
    input wire [63:0] inj_wide_b_1755327927347_670,
    input wire rst,
    output logic [3:0] cnt,
    output wire [127:0] inj_concat_out_1755327927347_427,
    output wire inj_o_1755327927318_827,
    output logic inj_out_a_1755327926996_303,
    output logic inj_out_c_1755327926597_759,
    output logic inj_out_l_1755327927422_888,
    output reg inj_out_res_1755327927134_581,
    output int inj_out_val_1755327926679_899,
    output logic [7:0] inj_out_val_e_1755327926794_252,
    output logic [7:0] inj_out_val_m10_1755327926899_456,
    output logic inj_q_1755327926598_87,
    output wire [7:0] inj_reduce_xor_out_1755327927347_628,
    output logic [7:0] inj_result_and_1755327926877_946,
    output logic [7:0] inj_result_and_1755327927243_949,
    output logic [7:0] inj_result_or_1755327926877_344,
    output logic [7:0] inj_result_or_1755327927243_40,
    output logic [7:0] inj_result_xor_1755327926877_731,
    output logic [7:0] inj_result_xor_1755327927243_76,
    output logic inj_status_e_1755327926794_433,
    output logic inj_tok_out_1755327926900_192,
    output wire [63:0] inj_wide_sum_1755327927347_424,
    output logic inj_write_status_1755327926605_259
);
    // BEGIN: ModClockedResetReg_ts1755327926598
    // BEGIN: local_not_allowed_diag_mod_ts1755327926679
    // BEGIN: BitwiseOperations_ts1755327926877
    // BEGIN: Module_MacroTokens_ts1755327926900
    // BEGIN: case_empty_statement_ts1755327927134
    // BEGIN: buf_primitive_ts1755327927318
    // BEGIN: wide_bus_ops_ts1755327927347
    // BEGIN: LintLatch_ts1755327927423
    always_comb begin
        if (inj_in_b_1755327926597_288) begin
            inj_out_l_1755327927422_888 = inj_in_a_1755327926597_456;
        end else begin
            inj_out_l_1755327927422_888 = 1'b0; 
        end
    end
    // END: LintLatch_ts1755327927423

    assign inj_wide_sum_1755327927347_424 = inj_wide_a_1755327927347_668 + inj_wide_b_1755327927347_670;
    assign inj_reduce_xor_out_1755327927347_628 = ^inj_wide_a_1755327927347_668[63:0];
    assign inj_concat_out_1755327927347_427 = {inj_wide_a_1755327927347_668, inj_wide_b_1755327927347_670};
    // END: wide_bus_ops_ts1755327927347

    buf b1 (inj_o_1755327927318_827, clk);
    // END: buf_primitive_ts1755327927318

    BitwiseOperations BitwiseOperations_inst_1755327927243_998 (
        .a(inj_c_1755327926877_515),
        .b(inj_wdata_1755327926605_780),
        .c(in_d),
        .result_and(inj_result_and_1755327927243_949),
        .result_or(inj_result_or_1755327927243_40),
        .result_xor(inj_result_xor_1755327927243_76)
    );
    always_comb begin
        inj_out_res_1755327927134_581 = 1'b0;
        case (inj_in_val_1755327927134_292)
            2'b00: inj_out_res_1755327927134_581 = 1'b1;
            2'b01: ;
            2'b10: inj_out_res_1755327927134_581 = 1'b0;
            default: inj_out_res_1755327927134_581 = 1'b1;
        endcase
    end
    // END: case_empty_statement_ts1755327927134

    mod_name_conflict mod_name_conflict_inst_1755327926996_9780 (
        .in_a(inj_in_a_1755327926597_456),
        .out_a(inj_out_a_1755327926996_303)
    );
    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = inj_in_b_1755327926597_288;
        inj_tok_out_1755327926900_192         = `PASTE(my,_var);
    end
    // END: Module_MacroTokens_ts1755327926900

    unsupported_cond_expr unsupported_cond_expr_inst_1755327926899_72 (
        .out_val_m10(inj_out_val_m10_1755327926899_456),
        .condition_m10(inj_condition_m10_1755327926899_772),
        .in_val_m10(inj_wdata_1755327926605_780)
    );
    assign inj_result_and_1755327926877_946 = in_d & inj_wdata_1755327926605_780;
    assign inj_result_or_1755327926877_344 = in_d | inj_c_1755327926877_515;
    assign inj_result_xor_1755327926877_731 = inj_wdata_1755327926605_780 ^ inj_c_1755327926877_515;
    // END: BitwiseOperations_ts1755327926877

    split_mixed_cond_seq split_mixed_cond_seq_inst_1755327926794_2914 (
        .condition_e(inj_in_a_1755327926597_456),
        .in_override_e(inj_wdata_1755327926605_780),
        .in_val_e(in_d),
        .out_val_e(inj_out_val_e_1755327926794_252),
        .status_e(inj_status_e_1755327926794_433),
        .clk_e(clk)
    );
    assign inj_out_val_1755327926679_899 = inj_in_val_1755327926679_968;
    // END: local_not_allowed_diag_mod_ts1755327926679

    module_sequential_writes module_sequential_writes_inst_1755327926605_4777 (
        .write_status(inj_write_status_1755327926605_259),
        .addr(in_d),
        .wdata(inj_wdata_1755327926605_780)
    );
    always @(posedge clk or negedge rst) begin
    if (!rst) begin
        inj_q_1755327926598_87 <= 1'b0;
    end else begin
        inj_q_1755327926598_87 <= inj_in_a_1755327926597_456;
    end
    end
    // END: ModClockedResetReg_ts1755327926598

    basic_assign_if basic_assign_if_inst_1755327926597_6165 (
        .in_a(inj_in_a_1755327926597_456),
        .in_b(inj_in_b_1755327926597_288),
        .out_c(inj_out_c_1755327926597_759)
    );
    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule


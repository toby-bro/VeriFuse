module loop_with_internal_assign (
    input logic [3:0] start_val,
    output logic [7:0] final_val
);
    logic [7:0] current_val;
    always_comb begin
        current_val = start_val;
        for (int k = 0; k < 3; k = k + 1) begin
            current_val = current_val + 1;
        end
        final_val = current_val;
    end
endmodule

module primitive_example (
    input logic i_p1,
    input logic i_p2,
    output logic o_p_and,
    output logic o_p_xor
);
    and (o_p_and, i_p1, i_p2);
    xor (o_p_xor, i_p1, i_p2);
endmodule

module wide_ops_deep (
    input logic [63:0] wide_a,
    input logic [63:0] wide_b,
    input logic [63:0] wide_c,
    output logic [63:0] wide_out
);
    assign wide_out = (((wide_a + wide_b) ^ wide_c) & (~wide_a | wide_b)) + (wide_c >>> 5);
endmodule

module countbits_ops #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic [7:0] in_d,
    input logic [7:0] inj_data2_1755327927048_859,
    input logic [7:0] inj_data3_1755327927048_672,
    input logic [15:0] inj_data_in_1755327926991_898,
    input wire [7:0] inj_i_in_1755327926544_780,
    input logic inj_i_p1_1755327926568_45,
    input logic inj_i_p2_1755327926568_809,
    input bit [3:0] inj_in_data_1755327926663_217,
    input logic [1:0] inj_sel_code_1755327927048_231,
    input logic [3:0] inj_start_val_1755327926552_878,
    input logic [63:0] inj_wide_a_1755327927255_788,
    input logic [63:0] inj_wide_b_1755327927268_588,
    input logic [63:0] inj_wide_c_1755327927268_34,
    input wire rst,
    output logic [3:0] cnt,
    output logic [15:0] inj_data_out_1755327926991_399,
    output logic [7:0] inj_final_val_1755327926552_676,
    output logic [7:0] inj_o_out_1755327926544_931,
    output logic inj_o_p_and_1755327926568_709,
    output logic inj_o_p_xor_1755327926568_112,
    output logic inj_o_sum_1755327926787_322,
    output logic inj_out1_1755327926632_57,
    output logic inj_out2_1755327926632_351,
    output logic [7:0] inj_out_if_a_1755327927122_56,
    output logic [7:0] inj_out_if_b_1755327927122_640,
    output bit [3:0] inj_out_result_1755327926663_344,
    output logic [7:0] inj_selected_data_1755327927048_911,
    output logic [63:0] inj_wide_out_1755327927268_852,
    output logic [63:0] inj_wide_out_1755327927324_1,
    output logic [7:0] inj_wide_reg_1755327926787_940
);
    // BEGIN: mod_module_attrs_ts1755327926544
    logic [WIDTH-1:0] r_data_ts1755327926544;
        // BEGIN: mod_lint_target_ts1755327926787
        logic l_reg_ts1755327926787;
            // BEGIN: mod_split_if_ts1755327927124
            logic [7:0]  split_if_var_ts1755327927124;
            logic [7:0] other_if_var_ts1755327927124;
                // BEGIN: wide_ops_deep_ts1755327927324
                assign inj_wide_out_1755327927324_1 = (((inj_wide_c_1755327927268_34 + inj_wide_b_1755327927268_588) ^ inj_wide_a_1755327927255_788) & (~inj_wide_c_1755327927268_34 | inj_wide_b_1755327927268_588)) + (inj_wide_a_1755327927255_788 >>> 5);
                // END: wide_ops_deep_ts1755327927324

                wide_ops_deep wide_ops_deep_inst_1755327927268_3341 (
                    .wide_b(inj_wide_b_1755327927268_588),
                    .wide_c(inj_wide_c_1755327927268_34),
                    .wide_out(inj_wide_out_1755327927268_852),
                    .wide_a(inj_wide_a_1755327927255_788)
                );
            always_ff @(posedge clk or posedge rst) begin
                if (rst) begin
                    split_if_var_ts1755327927124 <= 8'b0;
                    other_if_var_ts1755327927124 <= 8'b0;
                end else begin
                    if (inj_i_p2_1755327926568_809) begin
                        split_if_var_ts1755327927124 <= inj_data2_1755327927048_859;
                        other_if_var_ts1755327927124 <= inj_data2_1755327927048_859 + 3;
                    end else begin
                        split_if_var_ts1755327927124 <= inj_data2_1755327927048_859 - 1;
                        other_if_var_ts1755327927124 <= inj_data2_1755327927048_859 - 2;
                    end
                end
            end
            always_comb begin
                inj_out_if_a_1755327927122_56 = split_if_var_ts1755327927124;
                inj_out_if_b_1755327927122_640 = other_if_var_ts1755327927124;
            end
            // END: mod_split_if_ts1755327927124

            // BEGIN: IfElseIfChain_ts1755327927049
            always_comb begin
                if (inj_sel_code_1755327927048_231 == 2'b00) begin
                    inj_selected_data_1755327927048_911 = r_data_ts1755327926544;
                end else if (inj_sel_code_1755327927048_231 == 2'b01) begin
                    inj_selected_data_1755327927048_911 = in_d;
                end else if (inj_sel_code_1755327927048_231 == 2'b10) begin
                    inj_selected_data_1755327927048_911 = inj_data2_1755327927048_859;
                end else begin
                    inj_selected_data_1755327927048_911 = inj_data3_1755327927048_672;
                end
            end
            // END: IfElseIfChain_ts1755327927049

            // BEGIN: SequentialLogicPlaceholder_ts1755327927014
            always_ff @(posedge clk or posedge rst) begin
                if (rst) begin
                    inj_data_out_1755327926991_399 <= 16'h0;
                end else begin
                    inj_data_out_1755327926991_399 <= inj_data_in_1755327926991_898;
                end
            end
            // END: SequentialLogicPlaceholder_ts1755327927014

        always_comb begin
            l_reg_ts1755327926787 = 1;
            inj_wide_reg_1755327926787_940 = {clk, rst};
        end
        assign inj_o_sum_1755327926787_322 = clk + rst;
        // END: mod_lint_target_ts1755327926787

        // BEGIN: mod_if_else_simple_ts1755327926663
    always_comb begin
        if (inj_in_data_1755327926663_217 > 8) begin
            inj_out_result_1755327926663_344 = inj_in_data_1755327926663_217 + 1;
        end else begin
            inj_out_result_1755327926663_344 = inj_in_data_1755327926663_217 - 1;
        end
    end
        // END: mod_if_else_simple_ts1755327926663

        // BEGIN: module_unpacked_array_ts1755327926632
        logic [1:0] data_ua[0:1] ;
        always_comb begin
            data_ua[0][0] = inj_i_p1_1755327926568_45;
            data_ua[0][1] = inj_i_p2_1755327926568_809;
            data_ua[1][0] = data_ua[0][0];
            data_ua[1][1] = ~data_ua[0][1];
        end
        assign inj_out1_1755327926632_57 = data_ua[1][0];
        assign inj_out2_1755327926632_351 = data_ua[1][1];
        // END: module_unpacked_array_ts1755327926632

        primitive_example primitive_example_inst_1755327926568_8370 (
            .o_p_xor(inj_o_p_xor_1755327926568_112),
            .i_p1(inj_i_p1_1755327926568_45),
            .i_p2(inj_i_p2_1755327926568_809),
            .o_p_and(inj_o_p_and_1755327926568_709)
        );
        loop_with_internal_assign loop_with_internal_assign_inst_1755327926552_4898 (
            .final_val(inj_final_val_1755327926552_676),
            .start_val(inj_start_val_1755327926552_878)
        );
    always_comb begin
        r_data_ts1755327926544 = inj_i_in_1755327926544_780;
    end
    assign inj_o_out_1755327926544_931 = r_data_ts1755327926544;
    // END: mod_module_attrs_ts1755327926544

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule


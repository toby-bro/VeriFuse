module CaseEq (
    output wire match_x_neq,
    output wire match_z_eq,
    inout wire [3:0] data_io
);
    assign match_z_eq = (data_io === 4'b101z);
    assign match_x_neq = (data_io !== 4'b1x0x);
endmodule

module case_parallel_simple_mod (
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        (* parallel *)
        case (case_inside_val)
            4'd0, 4'd1: internal_out = 14;
            4'd2, 4'd3: internal_out = 15;
            default: internal_out = 18;
        endcase
    end
endmodule

module module_ternary (
    input wire in_cond_ternary,
    input wire [7:0] in_val1,
    input wire [7:0] in_val2,
    output logic [7:0] out_ternary_result
);
    always_comb begin
    out_ternary_result = in_cond_ternary ? in_val1 : in_val2;
    end
endmodule

module split_if_only_then (
    input logic clk_h,
    input logic condition_h,
    input logic [7:0] in_val_h,
    output logic [7:0] out_reg_h
);
    always @(posedge clk_h) begin
        if (condition_h) begin
            out_reg_h <= in_val_h;
        end
    end
endmodule

module simple_sub (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic inj_condition_h_1751608204132_423,
    input logic [3:0] inj_data0_1751608204137_416,
    input logic [3:0] inj_data1_1751608204137_850,
    input logic [3:0] inj_data2_1751608204137_376,
    input logic [3:0] inj_data3_1751608204137_768,
    input logic [15:0] inj_data_in_pa_1751608204130_326,
    input logic inj_enable_pv_1751608204130_819,
    input wire inj_in_cond_ternary_1751608204132_347,
    input wire [7:0] inj_in_val1_1751608204132_518,
    input wire [7:0] inj_in_val2_1751608204132_694,
    input logic [1:0] inj_large_data_in_1751608204135_837,
    output logic [3:0] inj_data_out_case_1751608204137_757,
    output logic [7:0] inj_data_out_pa_1751608204130_355,
    output logic [3:0] inj_data_out_pv_1751608204130_814,
    output logic [4:0] inj_internal_out_1751608204150_670,
    output logic [7:0] inj_large_sum_out_1751608204135_346,
    output wire inj_match_x_neq_1751608204147_458,
    output wire inj_match_z_eq_1751608204147_256,
    output logic [7:0] inj_out1_z_1751608204148_329,
    output logic [7:0] inj_out2_z_1751608204148_284,
    output logic [7:0] inj_out_1751608204130_793,
    output logic [3:0] inj_out_1751608204133_79,
    output logic [7:0] inj_out_reg_h_1751608204132_733,
    output logic [7:0] inj_out_ternary_result_1751608204132_418,
    output logic [8:0] sum,
    inout wire [3:0] inj_data_io_1751608204147_331
);
    // // BEGIN: multidriven_unhandled_ts1751608204130
    wire [7:0] conflict_wire_ts1751608204130;
    // // BEGIN: module_packed_variables_ts1751608204131
    // logic [31:0] data_pv_ts1751608204131 ;
    // logic [7:0] data_pa[0:1] ;
    // // BEGIN: loop_unroll_limit_test_ts1751608204136
    // logic [7:0] current_large_sum_ts1751608204136;
    // case_parallel_simple_mod case_parallel_simple_mod_inst_1751608204150_6962 (
    //     .case_inside_val(inj_data1_1751608204137_850),
    //     .internal_out(inj_internal_out_1751608204150_670)
    // );
    // // BEGIN: split_diff_vars_branches_ts1751608204149
    // always @(posedge inj_enable_pv_1751608204130_819) begin
    //     if (inj_condition_h_1751608204132_423) begin
    //         inj_out1_z_1751608204148_329 <= b;
    //     end else begin
    //         inj_out2_z_1751608204148_284 <= a;
    //     end
    // end
    // // END: split_diff_vars_branches_ts1751608204149

    // CaseEq CaseEq_inst_1751608204147_1101 (
    //     .match_x_neq(inj_match_x_neq_1751608204147_458),
    //     .match_z_eq(inj_match_z_eq_1751608204147_256),
    //     .data_io(inj_data_io_1751608204147_331)
    // );
    // // BEGIN: case_selector_ts1751608204143
    // always_comb begin
    //     case (inj_large_data_in_1751608204135_837)
    //         2'b00: inj_data_out_case_1751608204137_757 = inj_data0_1751608204137_416; 
    //         2'b01: inj_data_out_case_1751608204137_757 = inj_data1_1751608204137_850; 
    //         2'b10: inj_data_out_case_1751608204137_757 = inj_data2_1751608204137_376; 
    //         default: inj_data_out_case_1751608204137_757 = inj_data3_1751608204137_768; 
    //     endcase
    // end
    // END: case_selector_ts1751608204143
    // 
    // always_comb begin
    //     current_large_sum_ts1751608204136 = 8'h00;
    //     for (int m = 0; m < 40; m = m + 1) begin 
    //         current_large_sum_ts1751608204136 = current_large_sum_ts1751608204136 + inj_large_data_in_1751608204135_837[0];
    //         current_large_sum_ts1751608204136 = current_large_sum_ts1751608204136 + inj_large_data_in_1751608204135_837[1];
    //         current_large_sum_ts1751608204136 = current_large_sum_ts1751608204136 + 1;
    //     end
    //     inj_large_sum_out_1751608204135_346 = current_large_sum_ts1751608204136;
    // end
    // // END: loop_unroll_limit_test_ts1751608204136

    // // BEGIN: mismatched_width_unhandled_ts1751608204134
    // assign inj_out_1751608204133_79 = b;
    // END: mismatched_width_unhandled_ts1751608204134

    //split_if_only_then split_if_only_then_inst_1751608204132_1007 (
    //    .in_val_h(b),
    //    .out_reg_h(inj_out_reg_h_1751608204132_733),
    //    .clk_h(inj_enable_pv_1751608204130_819),
    //    .condition_h(inj_condition_h_1751608204132_423)
    //);
    //module_ternary module_ternary_inst_1751608204132_3568 (
    //    .out_ternary_result(inj_out_ternary_result_1751608204132_418),
    //    .in_cond_ternary(inj_in_cond_ternary_1751608204132_347),
    //    .in_val1(inj_in_val1_1751608204132_518),
    //    .in_val2(inj_in_val2_1751608204132_694)
    //);
    //always_comb begin
    //    if (inj_enable_pv_1751608204130_819) begin
    //        data_pv_ts1751608204131[7:0] = b;
    //        data_pv_ts1751608204131[15:8] = ~b;
    //        data_pv_ts1751608204131[23:16] = data_pv_ts1751608204131[7:0];
    //        data_pv_ts1751608204131[31:24] = data_pv_ts1751608204131[15:8];
    //        data_pa[0] = inj_data_in_pa_1751608204130_326[7:0];
    //        data_pa[1] = inj_data_in_pa_1751608204130_326[15:8];
    //    end else begin
    //        data_pv_ts1751608204131 = 32'h0;
    //        data_pa[0] = 8'h0;
    //        data_pa[1] = 8'h0;
    //    end
    //end
    //assign inj_data_out_pv_1751608204130_814 = data_pv_ts1751608204131[3:0];
    //assign inj_data_out_pa_1751608204130_355 = data_pa[0];
    //// END: module_packed_variables_ts1751608204131

    assign conflict_wire_ts1751608204130 = b;
    assign conflict_wire_ts1751608204130 = a;
    assign inj_out_1751608204130_793 = conflict_wire_ts1751608204130;
    // END: multidriven_unhandled_ts1751608204130

    assign sum = a - b;
endmodule


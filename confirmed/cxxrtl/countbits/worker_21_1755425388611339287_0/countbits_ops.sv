module case_priority_overlapping_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        priority casez (case_expr)
            2'b1?: internal_out = 5;
            2'b?1: internal_out = 6;  
            2'b0?: internal_out = 7;
            2'b?0: internal_out = 8;  
            default: internal_out = 9;
        endcase
    end
endmodule

module countbits_ops (
    input wire clk,
    input logic [7:0] in_d,
    input logic [1:0] inj_case_expr_1755425388977_720,
    input logic [2:0] inj_shift_val_1755425388976_868,
    input wire rst,
    output logic [3:0] cnt,
    output logic [4:0] inj_internal_out_1755425388977_412,
    output logic [7:0] inj_left_shift_log_1755425388976_490,
    output logic [7:0] inj_right_shift_arith_1755425388976_438,
    output logic [7:0] inj_right_shift_log_1755425388976_946
);
    // BEGIN: ShiftOperations_ts1755425388976
    case_priority_overlapping_mod case_priority_overlapping_mod_inst_1755425388977_1590 (
        .internal_out(inj_internal_out_1755425388977_412),
        .case_expr(inj_case_expr_1755425388977_720)
    );
    assign inj_left_shift_log_1755425388976_490 = in_d << inj_shift_val_1755425388976_868;
    assign inj_right_shift_log_1755425388976_946 = in_d >> inj_shift_val_1755425388976_868;
    assign inj_right_shift_arith_1755425388976_438 = $signed(in_d) >>> inj_shift_val_1755425388976_868;
    // END: ShiftOperations_ts1755425388976

    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule


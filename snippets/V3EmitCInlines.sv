function automatic int my_simple_func(input int mmsf_a, input int mmsf_b);
    return mmsf_a + mmsf_b * 2;
endfunction
class MySimpleClassForNew;
    logic [7:0] data_field;
    function new(logic [7:0] val);
        data_field = val;
    endfunction
    function logic [7:0] get_doubled_data();
        return data_field << 1;
    endfunction
endclass
module ModuleFuncCall (
    input int mmfc_in_a,
    input int mmfc_in_b,
    output int mmfc_out_sum
);
    int mmfc_temp_result;
    always_comb begin
        mmfc_temp_result = my_simple_func(mmfc_in_a, mmfc_in_b);
        mmfc_out_sum = mmfc_temp_result;
    end
endmodule
typedef struct packed {
    logic [7:0] field1;
    logic       field2;
} my_struct_t;
typedef logic [15:0] my_array_t [3:0];
module ModuleStructArr (
    input logic [1:0] mmsa_in_idx,
    input logic [7:0] mmsa_in_val,
    input logic mmsa_in_flag,
    output logic [15:0] mmsa_out_val
);
    my_struct_t mmsa_data_s;
    my_array_t  mmsa_data_a;
    logic [15:0] mmsa_temp_val;
    always_comb begin
        mmsa_data_s.field1 = mmsa_in_val;
        mmsa_data_s.field2 = mmsa_in_flag;
        mmsa_data_a[0] = 16'd10;
        mmsa_data_a[1] = {mmsa_data_s.field1, mmsa_data_s.field2 ? 8'hFF : 8'h00};
        mmsa_data_a[2] = 16'hABCD;
        mmsa_data_a[3] = {8'h55, 8'hAA};
        if (mmsa_in_idx < 4) begin
            mmsa_temp_val = mmsa_data_a[mmsa_in_idx];
        end else begin
            mmsa_temp_val = 16'b0;
        end
        mmsa_out_val = mmsa_temp_val;
    end
endmodule
module ModuleCase (
    input logic [1:0] mmcs_in_sel,
    input logic [7:0] mmcs_in_data,
    output logic [7:0] mmcs_out_data
);
    logic [7:0] mmcs_temp_data;
    always_comb begin
        case (mmcs_in_sel)
            2'b00: mmcs_temp_data = mmcs_in_data;
            2'b01: mmcs_temp_data = ~mmcs_in_data;
            2'b10: mmcs_temp_data = mmcs_in_data << 1;
            default: mmcs_temp_data = 8'hFF;
        endcase
        mmcs_out_data = mmcs_temp_data;
    end
endmodule
module ModuleOperators (
    input logic [7:0] mmo_in_a,
    input logic [7:0] mmo_in_b,
    output logic [15:0] mmo_out_result
);
    logic [15:0] mmo_temp_result;
    logic [7:0] mmo_bitwise_and;
    logic mmo_reduction_or;
    always_comb begin
        mmo_bitwise_and = mmo_in_a & mmo_in_b;
        mmo_reduction_or = |mmo_in_a;
        logic [7:0] mmo_xor_res = mmo_in_a ^ mmo_in_b;
        logic [7:0] mmo_or_res = mmo_in_a | mmo_in_b;
        logic [7:0] mmo_nand_res = ~(mmo_in_a & mmo_in_b);
        logic [7:0] mmo_nor_res = ~(mmo_in_a | mmo_in_b);
        logic [7:0] mmo_xnor_res = mmo_in_a ~^ mmo_in_b;
        logic mmo_eq_res = (mmo_in_a == mmo_in_b);
        logic mmo_ne_res = (mmo_in_a != mmo_in_b);
        logic mmo_gt_res = (mmo_in_a > mmo_in_b);
        logic mmo_lt_res = (mmo_in_a < mmo_in_b);
        logic mmo_log_and = mmo_eq_res && mmo_gt_res;
        logic mmo_log_or = mmo_ne_res || mmo_lt_res;
        mmo_temp_result = {mmo_bitwise_and, mmo_reduction_or, mmo_xor_res[6:0]};
        if (mmo_log_and) begin
             mmo_temp_result = {2{mmo_in_b[3:0], mmo_in_a[3:0]}} ^ {2{mmo_xor_res[3:0], mmo_or_res[3:0]}};
        end else if (mmo_log_or) begin
             mmo_temp_result = {mmo_in_a[7:4], mmo_in_b[7:4], mmo_nand_res[7:4], mmo_nor_res[7:4]};
        end else begin
             mmo_temp_result = {mmo_xnor_res, 8'hFF};
        end
        mmo_out_result = mmo_temp_result;
    end
endmodule
module ModuleFor (
    input logic [3:0] mmfl_in_limit,
    input logic [7:0] mmfl_in_data,
    output logic [15:0] mmfl_out_sum
);
    logic [15:0] mmfl_sum;
    int mmfl_i;
    always_comb begin
        mmfl_sum = 16'b0;
        for (mmfl_i = 0; mmfl_i < mmfl_in_limit && mmfl_i < 8; mmfl_i = mmfl_i + 1) begin
            mmfl_sum = mmfl_sum + {{8{mmfl_in_data[0]}}, mmfl_in_data} + (mmfl_in_data >> (mmfl_i % 8));
        end
        mmfl_out_sum = mmfl_sum;
    end
endmodule
module ModuleArith (
    input int mma_in_a,
    input byte mma_in_b,
    input shortint mma_in_c,
    input longint mma_in_d,
    output longint mma_out_result
);
    int mma_add_res;
    shortint mma_sub_res;
    shortint mma_mul_res;
    longint mma_div_res;
    longint mma_temp_res;
    always_comb begin
        mma_add_res = mma_in_a + mma_in_b;
        mma_sub_res = $shortint(mma_in_b) - mma_in_c;
        mma_mul_res = mma_in_c * mma_in_a;
        mma_div_res = 0;
        if (mma_in_a != 0) begin
            mma_div_res = mma_in_d / mma_in_a;
        end
        mma_temp_res = $longint(mma_add_res) + $longint(mma_sub_res) + $longint(mma_mul_res) + mma_div_res + mma_in_d;
        mma_out_result = mma_temp_res;
    end
endmodule
module ModuleCond (
    input logic mmc_in_sel,
    input logic [7:0] mmc_in_a,
    input logic [7:0] mmc_in_b,
    output logic [7:0] mmc_out_data
);
    always_comb begin
        mmc_out_data = mmc_in_sel ? mmc_in_a : mmc_in_b;
    end
endmodule
module ModuleBitShift (
    input logic [15:0] mmbs_in_data,
    input logic [3:0] mmbs_in_shift,
    input signed [15:0] mmbs_in_signed,
    output logic [15:0] mmbs_out_data
);
    logic [15:0] mmbs_temp_data;
    logic mmbs_and_reduce;
    logic mmbs_xor_reduce;
    logic [15:0] mmbs_left_shift;
    logic [15:0] mmbs_right_shift_log;
    signed [15:0] mmbs_right_shift_arith_res;
    always_comb begin
        mmbs_and_reduce = &mmbs_in_data;
        mmbs_xor_reduce = ^mmbs_in_data;
        mmbs_left_shift = mmbs_in_data << mmbs_in_shift;
        mmbs_right_shift_log = mmbs_in_data >> mmbs_in_shift;
        mmbs_right_shift_arith_res = mmbs_in_signed >>> mmbs_in_shift;
        if (mmbs_and_reduce) begin
            mmbs_temp_data = mmbs_left_shift & mmbs_right_shift_log;
        end else if (mmbs_xor_reduce) begin
            mmbs_temp_data = $unsigned(mmbs_right_shift_arith_res) | mmbs_left_shift;
        end else begin
            mmbs_temp_data = ~mmbs_in_data;
        end
        mmbs_out_data = mmbs_temp_data;
    end
endmodule
module ModuleAssign (
    input logic [7:0] mma_in_a,
    input logic [7:0] mma_in_b,
    output logic [7:0] mma_out_c
);
    logic [7:0] mma_wire_temp;
    logic [7:0] mma_reg_temp;
    assign mma_wire_temp = mma_in_a & mma_in_b;
    always_comb begin
        mma_reg_temp = mma_wire_temp | mma_in_a;
    end
    assign mma_out_c = mma_reg_temp ^ mma_in_b;
endmodule
module ModuleRepl (
    input logic [3:0] mmr_in_val,
    output logic [15:0] mmr_out_val
);
    logic [15:0] mmr_temp_val;
    always_comb begin
        mmr_temp_val = {4{mmr_in_val}};
    end
    assign mmr_out_val = mmr_temp_val;
endmodule
module ModuleSignedUnsigned (
    input signed [7:0] mmsu_in_signed_a,
    input logic [7:0] mmsu_in_unsigned_b,
    output logic [15:0] mmsu_out_result
);
    signed [15:0] mmsu_signed_mult;
    logic [15:0] mmsu_unsigned_mult;
    logic [15:0] mmsu_temp_result;
    always_comb begin
        mmsu_signed_mult = mmsu_in_signed_a * $signed(mmsu_in_unsigned_b);
        mmsu_unsigned_mult = $unsigned(mmsu_in_unsigned_b) * $unsigned(mmsu_in_unsigned_b);
        if (mmsu_in_signed_a > 0) begin
             mmsu_temp_result = $unsigned(mmsu_signed_mult);
        end else begin
             mmsu_temp_result = mmsu_unsigned_mult;
        end
        mmsu_out_result = mmsu_temp_result;
    end
endmodule
module ModuleChainedCond (
    input logic [1:0] mmcc_in_sel,
    input logic [7:0] mmcc_in_a,
    input logic [7:0] mmcc_in_b,
    input logic [7:0] mmcc_in_c,
    output logic [7:0] mmcc_out_data
);
    always_comb begin
        mmcc_out_data = (mmcc_in_sel == 2'b00) ? mmcc_in_a :
                        (mmcc_in_sel == 2'b01) ? mmcc_in_b :
                        mmcc_in_c;
    end
endmodule
module ModuleComplexExpr (
    input logic [7:0] mmce_in1,
    input logic [7:0] mmce_in2,
    input logic mmce_in_sel,
    output logic [15:0] mmce_out_result
);
    logic [15:0] mmce_temp1;
    logic [15:0] mmce_temp2;
    logic [15:0] mmce_result;
    always_comb begin
        mmce_temp1 = {mmce_in1, mmce_in2} + (mmce_in_sel ? 16'h10 : 16'h20) - ($unsigned(mmce_in1) | {8'b0, mmce_in2[0] ? 8'hFF : 8'h00}) + ({8'b0, mmce_in2} << 2);
        mmce_temp2 = ($unsigned(mmce_in1) & $unsigned(mmce_in2)) ^ (~$unsigned(mmce_in1)) | ({8'b0, mmce_in2} >>> 1);
        mmce_result = (mmce_temp1 > mmce_temp2) ? mmce_temp1 : mmce_temp2;
        mmce_out_result = mmce_result;
    end
endmodule
module ModuleComparison (
    input logic [7:0] mmc_in_a,
    input logic [7:0] mmc_in_b,
    output logic [5:0] mmc_out_results
);
    logic eq, ne, gt, lt, ge, le;
    always_comb begin
        eq = (mmc_in_a == mmc_in_b);
        ne = (mmc_in_a != mmc_in_b);
        gt = (mmc_in_a > mmc_in_b);
        lt = (mmc_in_a < mmc_in_b);
        ge = (mmc_in_a >= mmc_in_b);
        le = (mmc_in_a <= mmc_in_b);
        mmc_out_results = {eq, ne, gt, lt, ge, le};
    end
endmodule
module ModuleModulo (
    input int mmm_in_a,
    input int mmm_in_b,
    output int mmm_out_result
);
    int mmm_temp_result;
    always_comb begin
        mmm_temp_result = 0;
        if (mmm_in_b != 0) begin
            mmm_temp_result = mmm_in_a % mmm_in_b;
        end else begin
            mmm_temp_result = mmm_in_a;
        end
        mmm_out_result = mmm_temp_result;
    end
endmodule
module ModuleClassNew (
    input logic [7:0] mcnew_in_data,
    output logic [7:0] mcnew_out_processed
);
    MySimpleClassForNew my_instance;
    logic [7:0] temp_processed_data;
    always_comb begin
        my_instance = new(mcnew_in_data);
        if (my_instance != null) begin
            temp_processed_data = my_instance.get_doubled_data();
        end else begin
            temp_processed_data = 8'b0;
        end
    end
    assign mcnew_out_processed = temp_processed_data;
endmodule
module ModuleLogicalNot (
    input logic mmln_in_bool,
    input logic [7:0] mmln_in_vector,
    output logic mmln_out_bool_not,
    output logic [7:0] mmln_out_vector_not,
    output logic mmln_out_vector_is_zero
);
    always_comb begin
        mmln_out_bool_not = !mmln_in_bool;
        mmln_out_vector_not = ~mmln_in_vector;
        mmln_out_vector_is_zero = !(|mmln_in_vector);
    end
endmodule

module module_literals_assign (
  input logic [7:0] ma_in_logic_8,
  input int ma_in_int,
  input string ma_in_string,
  output logic [7:0] ma_out_logic_8_assign,
  output int ma_out_int_assign,
  output logic [15:0] ma_out_logic_16_assign_from_8,
  output logic [3:0] ma_out_logic_4_assign_from_8,
  output logic [7:0] ma_out_literal_hex,
  output logic [15:0] ma_out_literal_bin,
  output logic [31:0] ma_out_literal_dec_unsized,
  output logic [31:0] ma_out_literal_dec_sized,
  output logic [7:0] ma_out_literal_x_sized,
  output logic [7:0] ma_out_literal_z_sized,
  output string ma_out_string_assign,
  output logic [63:0] ma_out_literal_wide_hex,
  output real ma_out_literal_real
);
  always_comb begin
    ma_out_logic_8_assign = ma_in_logic_8;
    ma_out_int_assign = ma_in_int;
    ma_out_logic_16_assign_from_8 = ma_in_logic_8;
    ma_out_logic_4_assign_from_8 = ma_in_logic_8;
    ma_out_literal_hex = 'hF0;
    ma_out_literal_bin = 'b1010_1100_0101_0011;
    ma_out_literal_dec_unsized = 100;
    ma_out_literal_dec_sized = 32'd255;
    ma_out_literal_x_sized = 8'bx;
    ma_out_literal_z_sized = 8'bz;
    ma_out_string_assign = ma_in_string;
    ma_out_literal_wide_hex = 64'hFFFF_FFFF_FFFF_FFFF;
    ma_out_literal_real = 3.14;
  end
endmodule
module module_logic_scalar (
  input logic mls_in_log1,
  input logic mls_in_log2,
  output logic mls_out_log_not,
  output logic mls_out_log_and,
  output logic mls_out_log_or,
  output logic mls_out_log_if
);
  always_comb begin
    mls_out_log_not = !mls_in_log1;
    mls_out_log_and = mls_in_log1 && mls_in_log2;
    mls_out_log_or  = mls_in_log1 || mls_in_log2;
    mls_out_log_if  = mls_in_log1 -> mls_in_log2;
  end
endmodule
module module_equality_ops (
  input logic [7:0] meo_in_eq1,
  input logic [7:0] meo_in_eq2,
  input logic [7:0] meo_in_eq3,
  input logic [7:0] meo_in_eq4,
  output logic meo_out_eq,
  output logic meo_out_neq,
  output logic meo_out_case_eq,
  output logic meo_out_case_neq,
  output logic meo_out_wild_eq,
  output logic meo_out_wild_neq
);
  always_comb begin
    meo_out_eq        = meo_in_eq1 == meo_in_eq2;
    meo_out_neq       = meo_in_eq1 != meo_in_eq2;
    meo_out_case_eq   = meo_in_eq3 === meo_in_eq4;
    meo_out_case_neq  = meo_in_eq3 !== meo_in_eq4;
    meo_out_wild_eq   = meo_in_eq3 ==? meo_in_eq4;
    meo_out_wild_neq  = meo_in_eq3 !=? meo_in_eq4;
  end
endmodule
module module_comparison_ops (
  input logic [15:0] mco_in_comp1,
  input logic [15:0] mco_in_comp2,
  output logic mco_out_gt,
  output logic mco_out_lt,
  output logic mco_out_gte,
  output logic mco_out_lte
);
  always_comb begin
    mco_out_gt  = mco_in_comp1 > mco_in_comp2;
    mco_out_lt  = mco_in_comp1 < mco_in_comp2;
    mco_out_gte = mco_in_comp1 >= mco_in_comp2;
    mco_out_lte = mco_in_comp1 <= mco_in_comp2;
  end
endmodule
module module_signed_comparison_ops (
  input signed logic [15:0] msco_in_scomp1,
  input signed logic [15:0] msco_in_scomp2,
  output logic msco_out_sgt,
  output logic msco_out_slt,
  output logic msco_out_sgte,
  output logic msco_out_slte
);
  always_comb begin
    msco_out_sgt  = msco_in_scomp1 > msco_in_scomp2;
    msco_out_slt  = msco_in_scomp1 < msco_in_scomp2;
    msco_out_sgte = msco_in_scomp1 >= msco_in_scomp2;
    msco_out_slte = msco_in_scomp1 <= msco_in_scomp2;
  end
endmodule
module module_arithmetic_ops (
  input logic [15:0] mao_in_arith1,
  input logic [15:0] mao_in_arith2,
  output logic [15:0] mao_out_add,
  output logic [15:0] mao_out_sub,
  output logic [15:0] mao_out_mul,
  output logic [15:0] mao_out_div,
  output logic [15:0] mao_out_mod
);
  always_comb begin
    mao_out_add = mao_in_arith1 + mao_in_arith2;
    mao_out_sub = mao_in_arith1 - mao_in_arith2;
    mao_out_mul = mao_in_arith1 * mao_in_arith2;
    mao_out_div = mao_in_arith1 / (mao_in_arith2 == 0 ? 1 : mao_in_arith2);
    mao_out_mod = mao_in_arith1 % (mao_in_arith2 == 0 ? 1 : mao_in_arith2);
  end
endmodule
module module_signed_arithmetic_ops (
  input signed logic [15:0] msao_in_sarith1,
  input signed logic [15:0] msao_in_sarith2,
  output signed logic [15:0] msao_out_sadd,
  output signed logic [15:0] msao_out_ssub,
  output signed logic [15:0] msao_out_smul,
  output signed logic [15:0] msao_out_sdiv,
  output signed logic [15:0] msao_out_smod
);
  always_comb begin
    msao_out_sadd = msao_in_sarith1 + msao_in_sarith2;
    msao_out_ssub = msao_in_sarith1 - msao_in_sarith2;
    msao_out_smul = msao_in_sarith1 * msao_in_sarith2;
    msao_out_sdiv = msao_in_sarith1 / (msao_in_sarith2 == 0 ? 1 : msao_in_sarith2);
    msao_out_smod = msao_in_sarith1 % (msao_in_sarith2 == 0 ? 1 : msao_in_sarith2);
  end
endmodule
module module_wide_arithmetic_ops (
  input logic [127:0] mwao_in_wide1,
  input logic [127:0] mwao_in_wide2,
  output logic [127:0] mwao_out_wide_add,
  output logic [127:0] mwao_out_wide_sub,
  output logic [127:0] mwao_out_wide_mul,
  output logic [127:0] mwao_out_wide_div,
  output logic [127:0] mwao_out_wide_mod
);
  always_comb begin
    mwao_out_wide_add = mwao_in_wide1 + mwao_in_wide2;
    mwao_out_wide_sub = mwao_in_wide1 - mwao_in_wide2;
    mwao_out_wide_mul = mwao_in_wide1 * mwao_in_wide2;
    mwao_out_wide_div = mwao_in_wide1 / (mwao_in_wide2 == 0 ? 1 : mwao_in_wide2);
    mwao_out_wide_mod = mwao_in_wide1 % (mwao_in_wide2 == 0 ? 1 : mwao_in_wide2);
  end
endmodule
module module_power_op (
  input logic [7:0] mpo_in_base,
  input logic [3:0] mpo_in_exp,
  output logic [15:0] mpo_out_pow
);
  always_comb begin
    mpo_out_pow = mpo_in_base ** mpo_in_exp;
  end
endmodule
module module_signed_power_op (
  input signed logic [7:0] mspo_in_sbase,
  input signed logic [3:0] mspo_in_sexp,
  output signed logic [15:0] mspo_out_spow
);
  always_comb begin
    mspo_out_spow = mspo_in_sbase ** mspo_in_sexp;
  end
endmodule
module module_bitwise_ops (
  input logic [7:0] mbo_in_bit1,
  input logic [7:0] mbo_in_bit2,
  output logic [7:0] mbo_out_not_b,
  output logic [7:0] mbo_out_and_b,
  output logic [7:0] mbo_out_or_b,
  output logic [7:0] mbo_out_xor_b
);
  always_comb begin
    mbo_out_not_b = ~mbo_in_bit1;
    mbo_out_and_b = mbo_in_bit1 & mbo_in_bit2;
    mbo_out_or_b  = mbo_in_bit1 | mbo_in_bit2;
    mbo_out_xor_b = mbo_in_bit1 ^ mbo_in_bit2;
  end
endmodule
module module_reduction_ops (
  input logic [7:0] mro_in_red,
  output logic mro_out_red_and,
  output logic mro_out_red_or,
  output logic mro_out_red_xor,
  output logic mro_out_red_nand,
  output logic mro_out_red_nor,
  output logic mro_out_red_nxor
);
  always_comb begin
    mro_out_red_and  = &mro_in_red;
    mro_out_red_or   = |mro_in_red;
    mro_out_red_xor  = ^mro_in_red;
    mro_out_red_nand = ~&mro_in_red;
    mro_out_red_nor  = ~|mro_in_red;
    mro_out_red_nxor = ~^mro_in_red;
  end
endmodule
module module_shift_ops (
  input logic [15:0] mso_in_shift,
  input logic [3:0] mso_in_shamt,
  output logic [15:0] mso_out_shl,
  output logic [15:0] mso_out_shr,
  output logic [15:0] mso_out_shra
);
  always_comb begin
    mso_out_shl  = mso_in_shift << mso_in_shamt;
    mso_out_shr  = mso_in_shift >> mso_in_shamt;
    mso_out_shra = $signed(mso_in_shift) >>> mso_in_shamt;
  end
endmodule
module module_concat_repl (
  input logic [7:0] mcr_in_cat1,
  input logic [7:0] mcr_in_cat2,
  input logic [3:0] mcr_in_rep_val_unused,
  output logic [15:0] mcr_out_concat,
  output logic [31:0] mcr_out_repl
);
  parameter int REP_COUNT = 4;
  always_comb begin
    mcr_out_concat = {mcr_in_cat1, mcr_in_cat2};
    mcr_out_repl   = {REP_COUNT{mcr_in_cat1}};
  end
endmodule
module module_part_select (
  input logic [31:0] mps_in_sel,
  input logic [7:0] mps_in_sel_assign,
  output logic [7:0] mps_out_sel_static,
  output logic [7:0] mps_out_sel_plus,
  output logic [7:0] mps_out_sel_minus,
  output logic [31:0] mps_out_sel_assigned
);
  logic [31:0] temp_sel_assigned;
  always_comb begin
    mps_out_sel_static = mps_in_sel[15:8];
    mps_out_sel_plus  = mps_in_sel[8 +: 8];
    mps_out_sel_minus = mps_in_sel[15 -: 8];
    temp_sel_assigned = mps_in_sel;
    temp_sel_assigned[15:8] = mps_in_sel_assign;
    mps_out_sel_assigned = temp_sel_assigned;
  end
endmodule
module module_system_functions_logic (
  input logic [15:0] msfl_in_sys_logic,
  input int msfl_in_sys_int,
  output int msfl_out_clog2,
  output int msfl_out_countones,
  output logic msfl_out_isunknown,
  output logic msfl_out_onehot,
  output logic msfl_out_onehot0
);
  always_comb begin
    msfl_out_clog2    = $clog2(msfl_in_sys_int > 0 ? msfl_in_sys_int : 1);
    msfl_out_countones= $countones(msfl_in_sys_logic);
    msfl_out_isunknown= $isunknown(msfl_in_sys_logic);
    msfl_out_onehot   = $onehot(msfl_in_sys_logic);
    msfl_out_onehot0  = $onehot0(msfl_in_sys_logic);
  end
endmodule
module module_countbits (
  input logic [15:0] mcb_in_cb_val,
  input logic mcb_in_cb_ctrl1,
  input logic mcb_in_cb_ctrl2,
  input logic mcb_in_cb_ctrl3,
  output int mcb_out_countbits
);
  always_comb begin
    mcb_out_countbits = $countbits(mcb_in_cb_val, mcb_in_cb_ctrl1, mcb_in_cb_ctrl2, mcb_in_cb_ctrl3);
  end
endmodule
module module_string_basics (
  input string msb_in_str_in,
  output string msb_out_str_out,
  output int msb_out_str_len,
  output int msb_out_str_int_conv,
  output logic [7:0] msb_out_str_logic_conv,
  output logic [15:0] msb_out_str_wide_logic_conv
);
  string local_str_literal = "hello";
  always_comb begin
    msb_out_str_out = msb_in_str_in;
    msb_out_str_len = msb_in_str_in.len();
    msb_out_str_int_conv = int'(msb_in_str_in);
    msb_out_str_logic_conv = logic [7:0]'(msb_in_str_in);
    msb_out_str_wide_logic_conv = logic [15:0]'(msb_in_str_in);
  end
endmodule
module module_string_methods (
  input string msm_in_str_method,
  input int msm_in_str_idx,
  input int msm_in_str_char_val,
  input int msm_in_str_end_sub,
  input string msm_in_str_comp,
  output string msm_out_str_putc,
  output int msm_out_str_getc,
  output string msm_out_str_substr,
  output int msm_out_str_compare,
  output int msm_out_str_icompare,
  output string msm_out_str_lower,
  output string msm_out_str_upper
);
  string temp_str;
  always_comb begin
    temp_str = msm_in_str_method;
    temp_str.putc(msm_in_str_idx, msm_in_str_char_val);
    msm_out_str_putc = temp_str;
    msm_out_str_getc    = msm_in_str_method.getc(msm_in_str_idx);
    msm_out_str_substr  = msm_in_str_method.substr(msm_in_str_idx, msm_in_str_end_sub);
    msm_out_str_compare = msm_in_str_method.compare(msm_in_str_comp);
    msm_out_icompare= msm_in_str_method.icompare(msm_in_str_comp);
    msm_out_str_lower   = msm_in_str_method.tolower();
    msm_out_str_upper   = msm_in_str_method.toupper();
  end
endmodule
module module_sscanf (
  input string mss_in_sscanf_str,
  output int mss_out_sscanf_dec,
  output int mss_out_sscanf_hex,
  output int mss_out_sscanf_oct,
  output int mss_out_sscanf_bin,
  output real mss_out_sscanf_real
);
  int temp_dec, temp_hex, temp_oct, temp_bin;
  real temp_real;
  always_comb begin
    void'($sscanf(mss_in_sscanf_str, "%d", temp_dec));
    void'($sscanf(mss_in_sscanf_str, "%h", temp_hex));
    void'($sscanf(mss_in_sscanf_str, "%o", temp_oct));
    void'($sscanf(mss_in_sscanf_str, "%b", temp_bin));
    void'($sscanf(mss_in_sscanf_str, "%f", temp_real));
    mss_out_sscanf_dec = temp_dec;
    mss_out_sscanf_hex = temp_hex;
    mss_out_sscanf_oct = temp_oct;
    mss_out_sscanf_bin = temp_bin;
    mss_out_sscanf_real = temp_real;
  end
endmodule
module module_real_basics (
  input real mrb_in_real1,
  input real mrb_in_real2,
  output real mrb_out_real_add,
  output real mrb_out_real_sub,
  output real mrb_out_real_mul,
  output real mrb_out_real_div,
  output real mrb_out_real_pow
);
  real local_real = 1.23;
  always_comb begin
    mrb_out_real_add = mrb_in_real1 + mrb_in_real2;
    mrb_out_real_sub = mrb_in_real1 - mrb_in_real2;
    mrb_out_real_mul = mrb_in_real1 * mrb_in_real2;
    mrb_out_real_div = mrb_in_real1 / (mrb_in_real2 == 0.0 ? 1.0 : mrb_in_real2);
    mrb_out_real_pow = mrb_in_real1 ** mrb_in_real2;
  end
endmodule
module module_real_comparisons (
  input real mrc_in_rcomp1,
  input real mrc_in_rcomp2,
  output logic mrc_out_r_eq,
  output logic mrc_out_r_neq,
  output logic mrc_out_r_gt,
  output logic mrc_out_r_lt,
  output logic mrc_out_r_gte,
  output logic mrc_out_r_lte
);
  always_comb begin
    mrc_out_r_eq  = mrc_in_rcomp1 == mrc_in_rcomp2;
    mrc_out_r_neq = mrc_in_rcomp1 != mrc_in_rcomp2;
    mrc_out_r_gt  = mrc_in_rcomp1 > mrc_in_rcomp2;
    mrc_out_r_lt  = mrc_in_rcomp1 < mrc_in_rcomp2;
    mrc_out_r_gte = mrc_in_rcomp1 >= mrc_in_rcomp2;
    mrc_out_r_lte = mrc_in_rcomp1 <= mrc_in_rcomp2;
  end
endmodule
module module_real_conversions (
  input real mrconv_in_r_to_i,
  input logic [31:0] mrconv_in_i_to_r_u,
  input signed logic [31:0] mrconv_in_i_to_r_s,
  input longint mrconv_in_qi_to_r_s,
  input bit [63:0] mrconv_in_bits_to_r,
  output int mrconv_out_r_to_i_trunc,
  output longint mrconv_out_r_to_qi_trunc,
  output int mrconv_out_r_to_i_round,
  output real mrconv_out_i_to_r_u,
  output real mrconv_out_i_to_r_s,
  output real mrconv_out_qi_to_r_s,
  output real mrconv_out_bits_to_real,
  output bit [63:0] mrconv_out_real_to_bits
);
  always_comb begin
    mrconv_out_r_to_i_trunc = int'(mrconv_in_r_to_i);
    mrconv_out_r_to_qi_trunc = longint'(mrconv_in_r_to_i);
    mrconv_out_r_to_i_round = $round(mrconv_in_r_to_i);
    mrconv_out_i_to_r_u = real'(mrconv_in_i_to_r_u);
    mrconv_out_i_to_r_s = real'(mrconv_in_i_to_r_s);
    mrconv_out_qi_to_r_s = real'(mrconv_in_qi_to_r_s);
    mrconv_out_bits_to_real = $bitstoreal(mrconv_in_bits_to_r);
    mrconv_out_real_to_bits = $realtobits(mrconv_in_r_to_i);
  end
endmodule
module module_xz_propagation (
  input logic [7:0] mxzp_in_xz1,
  input logic [7:0] mxzp_in_xz2,
  input logic [3:0] mxzp_in_shift_amt_xz,
  output logic [7:0] mxzp_out_and_xz,
  output logic [7:0] mxzp_out_or_xz,
  output logic [7:0] mxzp_out_xor_xz,
  output logic [7:0] mxzp_out_not_xz,
  output logic [7:0] mxzp_out_shl_xz,
  output logic [7:0] mxzp_out_shr_xz,
  output logic [7:0] mxzp_out_add_xz,
  output logic mxzp_out_comp_eq_xz,
  output logic mxzp_out_comp_gt_xz,
  output logic mxzp_out_is_any_xz
);
  always_comb begin
    mxzp_out_and_xz = mxzp_in_xz1 & mxzp_in_xz2;
    mxzp_out_or_xz  = mxzp_in_xz1 | mxzp_in_xz2;
    mxzp_out_xor_xz = mxzp_in_xz1 ^ mxzp_in_xz2;
    mxzp_out_not_xz = ~mxzp_in_xz1;
    mxzp_out_shl_xz = mxzp_in_xz1 << mxzp_in_shift_amt_xz;
    mxzp_out_shr_xz = mxzp_in_xz1 >> mxzp_in_shift_amt_xz;
    mxzp_out_add_xz = mxzp_in_xz1 + mxzp_in_xz2;
    mxzp_out_comp_eq_xz = mxzp_in_xz1 == mxzp_in_xz2;
    mxzp_out_comp_gt_xz = mxzp_in_xz1 > mxzp_in_xz2;
    mxzp_out_is_any_xz = $isunknown(mxzp_in_xz1);
  end
endmodule
module module_tristate_logic (
  input logic mtl_in_tri_data,
  input logic mtl_in_tri_enable,
  output logic mtl_out_tristate
);
  always_comb begin
    mtl_out_tristate = mtl_in_tri_enable ? mtl_in_tri_data : 1'bz;
  end
endmodule
module module_stream_ops (
  input logic [31:0] mso_in_stream_val,
  output logic [31:0] mso_out_stream_l
);
  parameter int SLICE_SIZE = 8;
  always_comb begin
    mso_out_stream_l = { >> {SLICE_SIZE} mso_in_stream_val };
  end
endmodule
module module_mixed_width_type (
  input bit [7:0] mmwt_in_bit_8,
  input logic [15:0] mmwt_in_logic_16,
  input signed int mmwt_in_signed_int,
  input signed logic [31:0] mmwt_in_signed_logic_32,
  output logic [15:0] mmwt_out_assign_extend_zero,
  output signed logic [31:0] mmwt_out_assign_extend_signed,
  output logic [7:0] mmwt_out_assign_truncate,
  output logic [31:0] mmwt_out_op_mixed_width,
  output signed logic [31:0] mmwt_out_op_mixed_signed,
  output logic mmwt_out_op_mixed_type
);
  always_comb begin
    mmwt_out_assign_extend_zero = mmwt_in_bit_8;
    mmwt_out_assign_extend_signed = mmwt_in_signed_int;
    mmwt_out_assign_truncate = mmwt_in_logic_16;
    mmwt_out_op_mixed_width = {{16{1'b0}}, mmwt_in_bit_8} + mmwt_in_logic_16;
    mmwt_out_op_mixed_signed = mmwt_in_signed_logic_32 + $signed(mmwt_in_signed_int);
    mmwt_out_op_mixed_type = & (mmwt_in_bit_8 & mmwt_in_logic_16[7:0]);
  end
endmodule
module module_width_warning (
  input logic mww_dummy_in,
  output logic [3:0] mww_out_truncated_literal
);
  always_comb begin
    mww_out_truncated_literal = 8'hFF;
  end
endmodule

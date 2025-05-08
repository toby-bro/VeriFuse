module sv_literals (
  input wire [7:0] in_byte,
  output logic [15:0] out_sized,
  output logic [31:0] out_unsized,
  output logic [3:0] out_base,
  output logic [7:0] out_string_byte,
  output real out_real
);
  //INJECT
  assign out_sized = 16'hbeef;
  //INJECT
  assign out_unsized = 'd12345;
  //INJECT
  assign out_base = 4'b101x;
  always @* begin
    string my_string;
    my_string = "hello";
    //INJECT
    if (my_string.len() > 0) begin
      out_string_byte = my_string.getc(in_byte % my_string.len());
      //INJECT
    end else begin
      out_string_byte = 8'b0;
      //INJECT
    end
  end
  always @* begin
    out_real = 3.1415926535;
    //INJECT
  end
endmodule
module sv_logic_ops (
  input wire [7:0] in_a,
  input wire [7:0] in_b,
  output logic [7:0] out_and,
  output logic [7:0] out_or,
  output logic [7:0] out_xor,
  output logic [7:0] out_not,
  output logic out_log_and,
  output logic out_log_or,
  output logic out_log_not,
  output logic out_is_unknown
);
  assign out_and = in_a & in_b;
  //INJECT
  assign out_or = in_a | in_b;
  //INJECT
  assign out_xor = in_a ^ in_b;
  //INJECT
  assign out_not = ~in_a;
  //INJECT
  assign out_log_and = &(in_a);
  //INJECT
  assign out_log_or = |(in_b);
  //INJECT
  assign out_log_not = !(in_a);
  //INJECT
  assign out_is_unknown = $isunknown(in_a);
  //INJECT
endmodule
module sv_arithmetic_ops (
  input wire signed [15:0] in_a_s,
  input wire signed [15:0] in_b_s,
  input wire [15:0] in_a_u,
  input wire [15:0] in_b_u,
  output logic [15:0] out_add_u,
  output logic [15:0] out_sub_u,
  output logic [31:0] out_mul_u,
  output logic [15:0] out_div_u,
  output logic [15:0] out_mod_u,
  output logic signed [15:0] out_neg_s,
  output logic signed [15:0] out_add_s,
  output logic signed [15:0] out_sub_s,
  output logic signed [31:0] out_mul_s,
  output logic signed [15:0] out_div_s,
  output logic signed [15:0] out_mod_s
);
  assign out_add_u = in_a_u + in_b_u;
  //INJECT
  assign out_sub_u = in_a_u - in_b_u;
  //INJECT
  assign out_mul_u = in_a_u * in_b_u;
  //INJECT
  assign out_div_u = in_a_u / in_b_u;
  //INJECT
  assign out_mod_u = in_a_u % in_b_u;
  //INJECT
  assign out_neg_s = -in_a_s;
  //INJECT
  assign out_add_s = in_a_s + in_b_s;
  //INJECT
  assign out_sub_s = in_a_s - in_b_s;
  //INJECT
  assign out_mul_s = in_a_s * in_b_s;
  //INJECT
  assign out_div_s = in_a_s / in_b_s;
  //INJECT
  assign out_mod_s = in_a_s % in_b_s;
  //INJECT
endmodule
module sv_shift_ops (
  input wire [15:0] in_val,
  input wire [3:0] in_shift_u,
  input wire signed [3:0] in_shift_s,
  output logic [15:0] out_shl,
  output logic [15:0] out_shr,
  output logic signed [15:0] out_ashr
);
  assign out_shl = in_val << in_shift_u;
  //INJECT
  assign out_shr = in_val >> in_shift_u;
  //INJECT
  assign out_ashr = $signed(in_val) >>> in_shift_u;
  //INJECT
endmodule
module sv_comparison_ops (
  input wire [7:0] in_a,
  input wire [7:0] in_b,
  input wire signed [7:0] in_a_s,
  input wire signed [7:0] in_b_s,
  output logic out_eq,
  output logic out_neq,
  output logic out_case_eq,
  output logic out_case_neq,
  output logic out_wild_eq,
  output logic out_wild_neq,
  output logic out_gt_u,
  output logic out_gte_u,
  output logic out_lt_u,
  output logic out_lte_u,
  output logic out_gt_s,
  output logic out_gte_s,
  output logic out_lt_s,
  output logic out_lte_s
);
  assign out_eq = (in_a == in_b);
  //INJECT
  assign out_neq = (in_a != in_b);
  //INJECT
  assign out_case_eq = (in_a === in_b);
  //INJECT
  assign out_case_neq = (in_a !== in_b);
  //INJECT
  assign out_wild_eq = (in_a ==? 8'b01xz); 
  //INJECT
  assign out_wild_neq = (in_a !=? 8'b01xz); 
  //INJECT
  assign out_gt_u = (in_a > in_b);
  //INJECT
  assign out_gte_u = (in_a >= in_b);
  //INJECT
  assign out_lt_u = (in_a < in_b);
  //INJECT
  assign out_lte_u = (in_a <= in_b);
  //INJECT
  assign out_gt_s = (in_a_s > in_b_s);
  //INJECT
  assign out_gte_s = (in_a_s >= in_b_s);
  //INJECT
  assign out_lt_s = (in_a_s < in_b_s);
  //INJECT
  assign out_lte_s = (in_a_s <= in_b_s);
  //INJECT
endmodule
module sv_concat_repl (
  input wire [3:0] in_a,
  input wire [7:0] in_b,
  input wire [2:0] in_count,
  output logic [11:0] out_concat,
  output logic [15:0] out_repl
);
  parameter REPL_COUNT_CONST = 4;
  assign out_concat = {in_a, in_b};
  //INJECT
  assign out_repl = {REPL_COUNT_CONST{in_a}};
  //INJECT
endmodule
module sv_part_select (
  input wire [15:0] in_data,
  input wire [3:0] in_lsb,
  output logic [7:0] out_static_part,
  output logic [7:0] out_dynamic_part
);
  parameter DYN_WIDTH = 8;
  assign out_static_part = in_data[7:0];
  //INJECT
  assign out_dynamic_part = in_data[in_lsb +: DYN_WIDTH];
  //INJECT
endmodule
module sv_part_select_assign (
  input wire [15:0] in_base,
  input wire [7:0] in_value,
  input wire [3:0] in_lsb,
  output logic [15:0] out_data
);
  parameter DYN_WIDTH_ASSIGN = 8;
  always @* begin
    out_data = in_base;
    //INJECT
    out_data[in_lsb +: DYN_WIDTH_ASSIGN] = in_value;
    //INJECT
  end
endmodule
module sv_clog2_count_ones (
  input wire [15:0] in_val,
  input wire [1:0] in_ctrl_bit,
  output logic [3:0] out_clog2,
  output logic [4:0] out_count_ones,
  output logic [4:0] out_count_bits
);
  assign out_clog2 = $clog2(in_val);
  //INJECT
  assign out_count_ones = $countones(in_val);
  //INJECT
  logic [3:0] control;
  always @* begin
    case (in_ctrl_bit)
      2'b00: control = 4'b0000;
      2'b01: control = 4'b0001;
      2'b10: control = 4'b001x;
      2'b11: control = 4'b0x1z;
      default: control = 4'b0;
    endcase
    //INJECT
  end
  assign out_count_bits = $countbits(control[0], in_val);
  //INJECT
endmodule
module sv_string_ops (
  input string in_str1,
  input string in_str2,
  input int in_idx1,
  input int in_idx2,
  output string out_concat,
  output string out_repl,
  output string out_tolower,
  output string out_toupper,
  output string out_substr,
  output logic [7:0] out_getc,
  output int out_len,
  output int out_compare,
  output bit out_eq,
  output bit out_gt
);
  parameter REPL_COUNT = 2;
  assign out_concat = in_str1 + in_str2;
  //INJECT
  assign out_repl = {REPL_COUNT{in_str1}};
  //INJECT
  always @* begin
    string temp_str;
    int sv_length;
    temp_str = in_str1.tolower();
    //INJECT
    out_tolower = temp_str;
    temp_str = in_str1.toupper();
    //INJECT
    out_toupper = temp_str;
    sv_length = in_idx2 - in_idx1 + 1;
    if (in_idx1 < 0 || sv_length <= 0 || (in_idx1 + sv_length) > in_str1.len()) begin
        out_substr = "";
        //INJECT
    end else begin
        out_substr = in_str1.substr(in_idx1, sv_length);
        //INJECT
    end
    //INJECT
    if (in_idx1 < 0 || in_idx1 >= in_str1.len()) begin
        out_getc = 8'h0;
        //INJECT
    end else begin
        out_getc = in_str1.getc(in_idx1);
        //INJECT
    end
    //INJECT
  end
  assign out_len = in_str1.len();
  //INJECT
  assign out_compare = in_str1.compare(in_str2);
  //INJECT
  assign out_eq = (in_str1 == in_str2);
  //INJECT
  assign out_gt = (in_str1 > in_str2);
  //INJECT
endmodule
module sv_string_putc_task (
  input string in_str,
  input int in_idx,
  input byte in_char,
  output string out_str
);
  always @* begin
    string temp_str;
    temp_str = in_str;
    //INJECT
    if (in_idx >= 0 && in_idx < temp_str.len() && in_char != 0) begin
      temp_str.putc(in_idx, in_char);
      //INJECT
    end
    out_str = temp_str;
    //INJECT
  end
endmodule
module sv_type_conversion (
  input wire [15:0] in_int,
  input real in_real,
  input string in_string_packed,
  input string in_string_num,
  input real in_real64,
  input wire [63:0] in_bits64,
  output real out_int_to_real,
  output int out_real_to_int_trunc,
  output logic [63:0] out_real_to_bits64,
  output real out_bits_to_real64,
  output logic [15:0] out_string_to_int
);
  assign out_int_to_real = real'(in_int);
  //INJECT
  assign out_real_to_int_trunc = int'(in_real);
  //INJECT
  assign out_real_to_bits64 = $realtobits(in_real64);
  //INJECT
  assign out_bits_to_real64 = $bitstoreal(in_bits64);
  //INJECT
  assign out_string_to_int = in_string_packed; 
  //INJECT
endmodule
module sv_extend_truncate (
  input wire [7:0] in_small,
  input wire signed [7:0] in_small_s,
  output logic [15:0] out_extend_u,
  output logic signed [15:0] out_extend_s,
  output logic [3:0] out_truncate
);
  assign out_extend_u = in_small;
  //INJECT
  assign out_extend_s = $signed(in_small_s);
  //INJECT
  assign out_truncate = in_small;
  //INJECT
endmodule
module sv_power_op (
  input wire [3:0] in_base,
  input wire [2:0] in_exp,
  output logic [15:0] out_pow
);
  assign out_pow = in_base ** in_exp;
  //INJECT
endmodule
module sv_bufif1_gate (
  input wire in_data,
  input wire in_control,
  output logic out_data
);
  always @* begin
    if (in_control == 1'b1) begin
      out_data = in_data;
      //INJECT
    end else begin
      out_data = 1'bz;
      //INJECT
    end
  end
endmodule
module sv_streaming_op (
  input wire [15:0] in_packed_array,
  input wire [3:0] in_slice_size_in,
  output logic [15:0] out_streamed
);
  parameter REVERSAL_SLICE_SIZE = 8;
  parameter DATA_WIDTH = 16;
  assign out_streamed = { << REVERSAL_SLICE_SIZE { in_packed_array } };
  //INJECT
endmodule
module sv_real_ops (
  input real in_r1,
  input real in_r2,
  output real out_r_neg,
  output real out_r_add,
  output real out_r_sub,
  output real out_r_mul,
  output real out_r_div,
  output real out_r_pow,
  output bit out_r_eq,
  output bit out_r_neq,
  output bit out_r_gt,
  output bit out_r_gte,
  output bit out_r_lt,
  output bit out_r_lte
);
  assign out_r_neg = -in_r1;
  //INJECT
  assign out_r_add = in_r1 + in_r2;
  //INJECT
  assign out_r_sub = in_r1 - in_r2;
  //INJECT
  assign out_r_mul = in_r1 * in_r2;
  //INJECT
  assign out_r_div = in_r1 / in_r2;
  //INJECT
  assign out_r_pow = in_r1 ** in_r2;
  //INJECT
  assign out_r_eq = (in_r1 == in_r2);
  //INJECT
  assign out_r_neq = (in_r1 != in_r2);
  //INJECT
  assign out_r_gt = (in_r1 > in_r2);
  //INJECT
  assign out_r_gte = (in_r1 >= in_r2);
  //INJECT
  assign out_r_lt = (in_r1 < in_r2);
  //INJECT
  assign out_r_lte = (in_r1 <= in_r2);
  //INJECT
endmodule

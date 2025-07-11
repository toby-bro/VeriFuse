module simple_macro_user(input  logic in1, output logic [31:0] out1);
  `define SIMPLE_VALUE 32'd12345
  `define ANOTHER_SIMPLE (1 + 2)
  assign out1 = in1 ? (`SIMPLE_VALUE + `ANOTHER_SIMPLE) : 32'd0;
endmodule
module func_macro_args(input  int input_int, output int output_int);
  `define ADD(a, b)       ((a) + (b))
  `define SUBTRACT(x, y)  ((x) - (y))
  localparam int P1_ADD = `ADD(10, 20);
  int p2_sub_var;
  always_comb begin
    p2_sub_var = `SUBTRACT(50, input_int);
  end
  assign output_int = P1_ADD + p2_sub_var;
endmodule
module func_macro_defaults(input  logic en, output logic [7:0] default_out);
  `define DEFAULT_CONST       8'hAA
  `define CALC(val, def=`DEFAULT_CONST) ((val) | (def))
  localparam logic [7:0] P_WITH_DEF     = `CALC(8'h0F);
  localparam logic [7:0] P_OVERRIDE_DEF = `CALC(8'hF0, 8'h11);
  assign default_out = en ? P_WITH_DEF : P_OVERRIDE_DEF;
endmodule
module macro_stringification_user(input  logic sel, output string str_out);
  `define TO_STR(x) `"x`"
  `define TOKEN_NAME example_token
  localparam string S0 = `TO_STR(hello);
  localparam string S1 = `TO_STR(world_123);
  localparam string S2 = `TO_STR(`TOKEN_NAME);
  assign str_out = sel ? S0 : (sel ? S1 : S2);
endmodule
module macro_concat_user(input  logic [3:0] concat_in, output logic [7:0] concat_out);
  `define MAKE_NAME(a,b) a``b
  logic var_signal;
  always_comb begin
    `MAKE_NAME(var,_signal) = concat_in[0];
  end
  assign concat_out = {4'b0, concat_in[3:1], var_signal};
endmodule
module nested_macro_expansion(input  int in_val, output int out_val);
  `define LVL1(x) ((x) + 1)
  `define LVL2(y) `LVL1((y) * 2)
  `define LVL3(z) `LVL2((z) / 3)
  int nested_result;
  always_comb begin
    nested_result = `LVL3(`LVL1(in_val));
  end
  assign out_val = nested_result;
endmodule
module macro_line_continuation_user(input  logic lc_en, output logic [15:0] lc_val);
  `define MULTI_VAL                \
    16'hABCD
  `define ADD_FIVE(v)              \
    ((v) +                         \
     5)
  logic [15:0] value_reg;
  always_comb begin
    if (lc_en)
      value_reg = `MULTI_VAL;
    else
      value_reg = `ADD_FIVE(16'h0010);
  end
  assign lc_val = value_reg;
endmodule
module macro_redefinition_check(input  logic redefine_en, output int result_out);
  `define REDEF_NUM 10
  `define REDEF_NUM 20
  localparam int NUM_VAL = `REDEF_NUM;
  assign result_out = redefine_en ? NUM_VAL : 0;
endmodule
module builtin_macros_user(input  logic info_en, output string file_line_info);
  always_comb begin
    file_line_info = info_en ? {`__FILE__, ":", $sformatf("%0d", `__LINE__)} : "";
  end
endmodule
module recursive_macro_dummy(input logic in_bit, output logic out_bit);
  `define RECURSIVE_TEST `RECURSIVE_TEST
  assign out_bit = in_bit;
endmodule

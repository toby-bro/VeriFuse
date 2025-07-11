module UnaryOps (
    input  logic [7:0] in_vec,
    input  int         in_int,
    input  real        in_real,
    output logic [7:0] out_plus,
    output int         out_minus,
    output logic       out_log_not,
    output logic [7:0] out_bit_not,
    output logic       out_red_and,
    output int         out_preinc,
    output int         out_postdec,
    output real        out_real_predec,
    output real        out_real_postinc
);
    int  l_int;
    real l_real;
    always_comb begin
        out_plus         = +in_vec;
        out_minus        = -in_int;
        out_log_not      = !in_vec[0];
        out_bit_not      = ~in_vec;
        out_red_and      = &in_vec;
        l_int            = in_int;
        l_real           = in_real;
        out_preinc       = ++l_int;
        out_postdec      = l_int--;
        out_real_predec  = --l_real;
        out_real_postinc = l_real++;
    end
endmodule
module BinaryArithBitwiseOps (
    input  logic [15:0] a,
    input  logic [15:0] b,
    input  real         r_a,
    input  real         r_b,
    output logic [15:0] out_add,
    output logic [15:0] out_sub,
    output logic [15:0] out_mul,
    output logic [15:0] out_div,
    output logic [15:0] out_band,
    output logic [15:0] out_bor,
    output logic [15:0] out_bxor,
    output real         out_radd,
    output real         out_rmul,
    output logic        out_gt
);
    assign out_add  = a + b;
    assign out_sub  = a - b;
    assign out_mul  = a * b;
    assign out_div  = b == 0 ? 16'd0 : a / b;
    assign out_band = a & b;
    assign out_bor  = a | b;
    assign out_bxor = a ^ b;
    assign out_radd = r_a + r_b;
    assign out_rmul = r_a * r_b;
    assign out_gt   = a > b;
endmodule
module BinaryShiftPowerOps (
    input  logic [7:0]  val,
    input  logic [3:0]  sh,
    input  int          exp_val,
    input  int          exp_pow,
    output logic [7:0]  out_sll,
    output logic [7:0]  out_srl,
    output logic [7:0]  out_sal,
    output logic [7:0]  out_sar,
    output int          out_power
);
    assign out_sll   = val <<  sh;
    assign out_srl   = val >>  sh;
    assign out_sal   = val <<< sh;
    assign out_sar   = val >>> sh;
    assign out_power = exp_val ** exp_pow;
endmodule
module InsideOpNumeric (
    input  int  value_i,
    input  int  low_i,
    input  int  high_i,
    output logic inside_simple,
    output logic inside_list,
    output logic inside_reversed,
    output logic inside_unbounded
);
    assign inside_simple    = value_i inside { [low_i : high_i] };
    assign inside_list      = value_i inside { 1, 3, 5, 7 };
    assign inside_reversed  = value_i inside { [high_i : low_i] };
    assign inside_unbounded = value_i inside { [0 : $] };
endmodule
module ConcatVectorOps (
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic [7:0] c,
    output logic [15:0] out_concat
);
    assign out_concat = {a, b, c};
endmodule
module ReplicationOps (
    input  logic [7:0] vec_in,
    input  int         count_in,
    output logic [63:0] out_repl_const,
    output logic [63:0] out_repl_var
);
    assign out_repl_const = {8{vec_in}};
    always_comb begin
        integer idx;
        out_repl_var = '0;
        for (idx = 0; idx < (count_in > 8 ? 8 : count_in); idx = idx + 1) begin
            out_repl_var[idx*8 +: 8] = vec_in;
        end
    end
endmodule
module ConditionalOps (
    input  logic sel,
    input  int   val_true,
    input  int   val_false,
    output int   out_val
);
    assign out_val = sel ? val_true : val_false;
endmodule

module simple_assign (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule
module always_comb_assign (
    input logic [15:0] in,
    output logic [15:0] out
);
    always_comb begin
        out = in;
    end
endmodule
module always_comb_if (
    input logic [31:0] in1,
    input logic [31:0] in2,
    input logic cond,
    output logic [31:0] out
);
    always_comb begin
        if (cond) begin
            out = in1;
        end else begin
            out = in2;
        end
    end
endmodule
module bitwise_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic [7:0] out
);
    assign out = (in1 & in2) | (~in3) ^ (in1 << 2) >> 1;
endmodule
module arith_comp_ops (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [15:0] in3,
    input logic [15:0] in4,
    input logic [15:0] in5,
    output logic out
);
    assign out = (in1 + in2) * in3 > in4 - in5;
endmodule
module reduction_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic out
);
    assign out = &in1 | ^in2;
endmodule
module constant_sel (
    input logic [31:0] in,
    output logic [7:0] out1,
    output logic out2
);
    assign out1 = in[15:8];
    assign out2 = in[3];
endmodule
module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
endmodule
module concat_op (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out_c
);
    assign out_c = {in_h, in_l};
endmodule
module concat_assign (
    input logic [7:0] in,
    output logic [3:0] out_h,
    output logic [3:0] out_l
);
    assign {out_h, out_l} = in;
endmodule
module array_assign_unhandled (
    input logic [7:0] in,
    input logic [1:0] index,
    output logic [7:0] out
);
    logic [7:0] data_arr [0:3];
    always_comb begin
        data_arr[index] = in;
    end
    assign out = data_arr[0];
endmodule
module timed_assign_unhandled (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule
module multidriven_unhandled (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out
);
    wire [7:0] conflict_wire;
    assign conflict_wire = in1;
    assign conflict_wire = in2;
    assign out = conflict_wire;
endmodule
module mismatched_width_unhandled (
    input logic [7:0] in,
    output logic [3:0] out
);
    assign out = in;
endmodule
module always_multi_stmt_unhandled (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    always_comb begin
        out1 = in1;
        out2 = in2;
    end
endmodule
module more_ops (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic [7:0] sum,
    output logic diff,
    output logic anded,
    output logic ored,
    output logic xored
);
    assign sum = a + b;
    assign diff = a > c;
    assign anded = a & b;
    assign ored = a | c;
    assign xored = a ^ b;
endmodule
module shift_ops (
    input logic [7:0] data,
    input logic [2:0] shamt,
    output logic [7:0] left_shift,
    output logic [7:0] right_shift_logic,
    output logic [7:0] right_shift_arith
);
    assign left_shift = data << shamt;
    assign right_shift_logic = data >> shamt;
    assign right_shift_arith = data >>> shamt;
endmodule
module equality_ops (
    input logic [7:0] a,
    input logic [7:0] b,
    output logic eq,
    output logic neq,
    output logic case_eq,
    output logic case_neq
);
    localparam logic [7:0] Z_VAL = 'z;
    localparam logic [7:0] X_VAL = 'x;
    assign eq = a == b;
    assign neq = a != b;
    assign case_eq = (a ==? Z_VAL);
    assign case_neq = (b !=? X_VAL);
endmodule
module div_mod_ops (
    input logic [15:0] numerator,
    input logic [7:0] denominator,
    input logic [15:0] dividend_mod,
    input logic [7:0] divisor_mod,
    output logic [15:0] quotient,
    output logic [7:0] remainder
);
    assign quotient = numerator / denominator;
    assign remainder = dividend_mod % divisor_mod;
endmodule
module remaining_reduction_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic nand_out,
    output logic nor_out,
    output logic xnor_out
);
    assign nand_out = ~&in1;
    assign nor_out = ~|in2;
    assign xnor_out = ^~in3;
endmodule
module function_call_op (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out
);
    function automatic logic [7:0] add_values (input logic [7:0] val1, input logic [7:0] val2);
        return val1 + val2;
    endfunction
    assign out = add_values(in1, in2);
endmodule
module sequential_always_assign (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule
module coalesced_assign (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out
);
    wire [7:0] temp_wire;
    assign temp_wire[7:4] = in_h;
    assign temp_wire[3:0] = in_l;
    assign out = temp_wire;
endmodule

module AlwaysStar_Combo (
    input bit [7:0] in_data,
    input bit in_en,
    output bit [7:0] out_combo
);
    always @* begin
        //INJECT
        if (in_en) begin
            out_combo = in_data;
        end else begin
            out_combo = 8'h00;
        end
        //INJECT
    end
endmodule
module AlwaysPosEdge_Seq (
    input bit clk,
    input bit rst_n,
    input bit [3:0] in_seq_data,
    output logic [3:0] out_q
);
    always @(posedge clk or negedge rst_n) begin
        //INJECT
        if (!rst_n) begin
            out_q <= 4'h0;
        end else begin
            out_q <= in_seq_data;
        end
        //INJECT
    end
endmodule
module AlwaysLatch_Inferred (
    input bit enable,
    input bit [1:0] data_in,
    output logic [1:0] latched_q
);
    always_latch begin
        //INJECT
        if (enable) begin
            latched_q = data_in;
        end
        //INJECT
    end
endmodule
module AlwaysComb_Explicit (
    input bit [2:0] a,
    input bit [2:0] b,
    output logic [2:0] out_sum
);
    always_comb begin
        //INJECT
        out_sum = a + b;
        //INJECT
    end
endmodule
module AlwaysFF_Explicit (
    input bit clk,
    input bit [5:0] d,
    output logic [5:0] q_ff
);
    always_ff @(posedge clk) begin
        //INJECT
        q_ff <= d;
        //INJECT
    end
endmodule
module ContinuousAssign (
    input bit [3:0] data_in,
    output wire [3:0] data_out
);
    //INJECT
    assign data_out = data_in;
    //INJECT
endmodule
module ComboIfElse_LatchCheck (
    input bit control_signal,
    input bit [4:0] input_val,
    output logic [4:0] output_reg
);
    always @* begin
        //INJECT
        if (control_signal) begin
            output_reg = input_val;
        end else begin 
            output_reg = 5'h00;
        end
        //INJECT
    end
endmodule
module SeqBlockingWarn ( 
    input bit clk,
    input bit [7:0] data_in,
    output logic [7:0] data_out_seq
);
    always @(posedge clk) begin
        //INJECT
        data_out_seq <= data_in; 
        //INJECT
    end
endmodule
module ComboNonBlockingWarn ( 
    input bit [15:0] operand_a,
    input bit [15:0] operand_b,
    output logic [15:0] result_comb
);
    always @* begin
        //INJECT
        result_comb = operand_a + operand_b; 
        //INJECT
    end
endmodule
module ModuleWithTask (
    input bit [7:0] val_in,
    input bit task_en,
    output logic [7:0] val_out
);
    task apply_transform;
        input bit [7:0] data;
        output logic [7:0] result;
        //INJECT
        result = data ^ 8'hF0;
        //INJECT
    endtask
    always @* begin
        //INJECT
        if (task_en) begin
            apply_transform(val_in, val_out);
        end else begin
            val_out = 8'h00;
        end
        //INJECT
    end
endmodule
module ModuleWithFunction (
    input bit [3:0] func_a,
    input bit [3:0] func_b,
    output bit [4:0] func_result
);
    function automatic bit [4:0] add_saturate;
        input bit [3:0] op1;
        input bit [3:0] op2;
        bit [4:0] sum;
        //INJECT
        sum = {1'b0, op1} + {1'b0, op2};
        if (sum > 5'd15) sum = 5'd15;
        return sum;
        //INJECT
    endfunction
    //INJECT
    assign func_result = add_saturate(func_a, func_b);
    //INJECT
endmodule
module AlwaysCase_Decode (
    input bit [2:0] opcode,
    input bit [7:0] data_val,
    output logic [7:0] result_case
);
    always_comb begin
        //INJECT
        case (opcode)
            3'h0: result_case = data_val;
            3'h1: result_case = data_val + 1;
            3'h2: result_case = data_val - 1;
            default: result_case = 8'hXX;
        endcase
        //INJECT
    end
endmodule
module ParameterUsage_Logic (
    input bit [7:0] data_in_p,
    input bit param_en,
    output logic [7:0] data_out_p
);
    parameter MY_PARAM = 8'hAA;
    //INJECT
    always @* begin
        //INJECT
        if (param_en) begin
            data_out_p = data_in_p ^ MY_PARAM;
        end else begin
            data_out_p = data_in_p;
        end
        //INJECT
    end
endmodule
module SignedArithmetic_Comb (
    input signed [7:0] in_a,
    input signed [7:0] in_b,
    output signed [8:0] out_sum_signed
);
    //INJECT
    assign out_sum_signed = in_a + in_b;
    //INJECT
endmodule
module ArrayAccess_Seq (
    input bit clk,
    input bit [1:0] addr,
    input bit [3:0] write_data,
    input bit write_en,
    output logic [3:0] read_data
);
    logic [3:0] my_array [0:3];
    //INJECT
    always_ff @(posedge clk) begin
        //INJECT
        if (write_en) begin
            my_array[addr] <= write_data;
        end
        read_data <= my_array[addr];
        //INJECT
    end
endmodule
module GenerateIf_Config (
    input bit gen_if_in,
    input bit gen_if_sel,
    output logic gen_if_out
);
    parameter CONFIG_MODE = 1; 
    //INJECT
    generate
        if (CONFIG_MODE == 1) begin : mode1_gen
            assign gen_if_out = gen_if_in & gen_if_sel;
            //INJECT
        end else begin : mode0_gen
            assign gen_if_out = gen_if_in | gen_if_sel;
            //INJECT
        end
    endgenerate
endmodule
module GenerateFor_Assigns (
    input bit [3:0] gen_for_in,
    output wire [3:0] gen_for_out
);
    //INJECT
    generate
        genvar i;
        for (i = 0; i < 4; i = i + 1) begin : bit_invert
            assign gen_for_out[i] = ~gen_for_in[i];
            //INJECT
        end
    endgenerate
endmodule
module BitPartSelect (
    input bit [15:0] data_wide_in,
    input bit [2:0] bit_idx,
    output wire [7:0] part_out,
    output wire bit_out
);
    //INJECT
    assign part_out = data_wide_in[7:0];
    assign bit_out = data_wide_in[bit_idx];
    //INJECT
endmodule

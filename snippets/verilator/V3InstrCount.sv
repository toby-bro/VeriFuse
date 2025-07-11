module module_selection (
    input wire [7:0] in_vector,
    input wire [2:0] in_index,
    input wire [1:0] in_part_lsb,
    input wire in_bit,
    output logic [7:0] out_vector_assign,
    output logic out_bit_select,
    output logic [3:0] out_part_select,
    output logic [7:0] out_bitwise_ops
);
always_comb begin
    out_vector_assign = in_vector;
    out_bit_select = in_vector[in_index];
    out_part_select = in_vector[in_part_lsb +: 4];
    out_bitwise_ops = in_vector & {8{in_bit}};
end
endmodule
module module_concat_if (
    input wire [3:0] in_a,
    input wire [3:0] in_b,
    input wire [7:0] in_c,
    input wire in_cond_if,
    output logic [15:0] out_concat,
    output logic [7:0] out_if_else
);
always_comb begin
    out_concat = {in_a, in_b, in_c};
    if (in_cond_if) begin
        out_if_else = in_c;
    end else begin
        out_if_else = {in_a, in_b};
    end
end
endmodule
module module_ternary (
    input wire [7:0] in_val1,
    input wire [7:0] in_val2,
    input wire in_cond_ternary,
    output logic [7:0] out_ternary_result
);
always_comb begin
    out_ternary_result = in_cond_ternary ? in_val1 : in_val2;
end
endmodule
module module_function (
    input wire [7:0] in_func_a,
    input wire [7:0] in_func_b,
    output logic [7:0] out_func_result
);
function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp;
begin
    temp = val1 + val2;
    add_and_subtract = temp - 1;
end
endfunction
always_comb begin
    out_func_result = add_and_subtract(in_func_a, in_func_b);
end
endmodule
module module_task (
    input wire in_task_clk,
    input wire in_task_rst,
    input wire [3:0] in_task_data,
    output reg [3:0] out_task_reg
);
task automatic compute_next_reg_value;
    input [3:0] current_reg;
    input [3:0] data_in;
    input logic rst_n;
    output [3:0] next_reg_value;
begin
    if (!rst_n) begin
        next_reg_value = 4'b0;
    end else begin
        next_reg_value = data_in;
    end
end
endtask
always_ff @(posedge in_task_clk or negedge in_task_rst) begin
    reg [3:0] next_val;
    compute_next_reg_value(out_task_reg, in_task_data, !in_task_rst, next_val);
    out_task_reg <= next_val;
end
endmodule
module module_fork_join (
    input wire in_fj_clk,
    input wire in_fj_start,
    output reg [7:0] out_fj_result
);
always_ff @(posedge in_fj_clk) begin
    if (in_fj_start) begin
        fork
            begin
                out_fj_result[3:0] <= 4'b1111;
            end
            begin
                out_fj_result[7:4] <= 4'b1010;
            end
        join
    end else begin
        out_fj_result <= 8'b0;
    end
end
endmodule
module module_latch (
    input wire [7:0] in_latch_data,
    input wire in_latch_en,
    output reg [7:0] out_latch_reg
);
always_latch begin
    if (in_latch_en) begin
        out_latch_reg = in_latch_data;
    end
end
endmodule

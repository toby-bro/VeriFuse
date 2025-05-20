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


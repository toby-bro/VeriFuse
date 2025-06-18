module deep_task_logic (
    input wire [1:0] dtl_action_sel,
    input wire dtl_clk,
    input wire [7:0] dtl_data_a,
    input wire [7:0] dtl_data_b,
    input wire dtl_en,
    input wire dtl_rst_n,
    output logic [7:0] dtl_result_reg
);
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res;
        logic [7:0] temp_task_calc;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc = in_a + in_b;
            end else begin
                temp_task_calc = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc = in_a & in_b;
            end else begin
                temp_task_calc = in_a | in_b;
            end
        end
        case (temp_task_calc[1:0])
            2'b00: calculated_res = temp_task_calc ^ 8'hFF;
            2'b01: calculated_res = temp_task_calc + 1;
            2'b10: calculated_res = temp_task_calc - 1;
            default: calculated_res = temp_task_calc;
        endcase
    endtask
    always_ff @(posedge dtl_clk or negedge dtl_rst_n) begin
        if (!dtl_rst_n) begin
            dtl_result_reg <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result;
            if (dtl_en) begin
                perform_action(dtl_data_a, dtl_data_b, dtl_action_sel, next_dtl_result);
            end else begin
                next_dtl_result = dtl_result_reg;
            end
            dtl_result_reg <= next_dtl_result;
        end
    end
endmodule


module deep_loop_with_conditionals (
    input wire [3:0] dlwc_break_at,
    input wire [3:0] dlwc_continue_at,
    input wire [7:0] dlwc_data_in,
    input wire [3:0] dlwc_limit,
    output logic [7:0] dlwc_output_sum
);
    always_comb begin
        logic [7:0] sum_val = 8'd0;
        integer i;
        for (i = 0; i < dlwc_limit; i = i + 1) begin
            if (i == dlwc_break_at) begin
                sum_val = sum_val | dlwc_data_in;
                break;
            end
            if (i == dlwc_continue_at) begin
                sum_val = sum_val + {4'b0, dlwc_limit};
                continue;
            end
            case (i[1:0])
                2'b00: sum_val = sum_val + dlwc_data_in;
                2'b01: sum_val = sum_val ^ dlwc_data_in;
                2'b10: sum_val = sum_val & dlwc_data_in;
                default: sum_val = sum_val | dlwc_data_in;
            endcase
        end
        dlwc_output_sum = sum_val;
    end
endmodule


module module_repeat_loop (
    input logic [7:0] in_add_val,
    input logic [3:0] in_repeat_count,
    output logic [15:0] out_total
);
    parameter int REPEAT_PARAM = 5;
    logic [15:0] total_sum;
    always_comb begin
        total_sum = 16'b0;
        repeat (REPEAT_PARAM) begin
            total_sum = total_sum + in_add_val;
        end
    end
    assign out_total = total_sum;
endmodule


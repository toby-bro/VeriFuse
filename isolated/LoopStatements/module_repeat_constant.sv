module module_repeat_constant (
    input logic [7:0] in_val,
    output logic [15:0] out_sum
);
    parameter int CONST_REPEAT = 7;
    logic [15:0] sum_val;
    always_comb begin
        sum_val = 16'b0;
        repeat (CONST_REPEAT)
            sum_val += in_val;
    end
    assign out_sum = sum_val;
endmodule


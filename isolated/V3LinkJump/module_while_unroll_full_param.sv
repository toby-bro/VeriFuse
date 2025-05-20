module module_while_unroll_full_param (
    input logic dummy_in,
    output logic [7:0] out_sum
);
    parameter PARAM_COUNT = 8;
    always_comb begin: while_unroll_block
        logic [3:0] i;
        out_sum = 0;
        i = 0;
        while (i < PARAM_COUNT) begin
            out_sum = out_sum + i;
            i = i + 1;
        end
    end
endmodule


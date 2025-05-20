module module_loop_idx_used (
    input logic [3:0] in_limit,
    output logic [7:0] out_sum_idx
);
    always_comb begin: loop_idx_block
        out_sum_idx = 0;
        for (int i = 0; i < in_limit; i = i + 1) begin
             out_sum_idx = out_sum_idx + i;
        end
    end
endmodule


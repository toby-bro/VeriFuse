module module_foreach_continue (
    input logic [7:0] in_skip,
    output logic [7:0] out_sum_filtered,
    input logic [7:0] in_seed
);
    logic [3:0][7:0] internal_array; 
    always_comb begin: foreach_cont_block
        for (int k = 0; k < 4; k++) begin
            internal_array[k] = in_seed + k;
        end
        out_sum_filtered = 0;
        foreach (internal_array[idx]) begin
            if (internal_array[idx] == in_skip) begin
                continue;
            end
            out_sum_filtered = out_sum_filtered + internal_array[idx];
        end
    end
endmodule


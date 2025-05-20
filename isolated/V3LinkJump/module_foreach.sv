module module_foreach (
    input logic [7:0] in_seed,
    output logic [7:0] out_sum_array
);
    logic [3:0][7:0] internal_array; 
    always_comb begin: foreach_block
        for (int k = 0; k < 4; k++) begin
            internal_array[k] = in_seed + k;
        end
        out_sum_array = 0;
        foreach (internal_array[idx]) begin
            out_sum_array = out_sum_array + internal_array[idx];
        end
    end
endmodule


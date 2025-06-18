module module_foreach_break (
    input logic [7:0] in_seed,
    input logic [7:0] in_stop,
    output logic [7:0] out_sum_partial
);
    logic [3:0][7:0] internal_array; 
    always_comb begin: foreach_break_block
        for (int k = 0; k < 4; k++) begin
            internal_array[k] = in_seed + k;
        end
        out_sum_partial = 0;
        foreach (internal_array[idx]) begin
            if (internal_array[idx] == in_stop) begin
                break;
            end
            out_sum_partial = out_sum_partial + internal_array[idx];
        end
    end
endmodule


module loop_unroll_limit_test (
    output logic [7:0] large_sum_out,
    input logic [1:0] large_data_in
);
    logic [7:0] current_large_sum;
    always_comb begin
        current_large_sum = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum = current_large_sum + large_data_in[0];
            current_large_sum = current_large_sum + large_data_in[1];
            current_large_sum = current_large_sum + 1;
        end
        large_sum_out = current_large_sum;
    end
endmodule


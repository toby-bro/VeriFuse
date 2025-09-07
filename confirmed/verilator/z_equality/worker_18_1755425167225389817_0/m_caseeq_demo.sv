module m_caseeq_demo (
    input wire clk,
    input logic in,
    input logic [1:0] inj_large_data_in_1755425167553_111,
    input wire rst,
    output logic eq,
    output logic [7:0] inj_large_sum_out_1755425167553_885,
    output logic neq
);
    logic tri_sig = 1'bz;
    // BEGIN: loop_unroll_limit_test_ts1755425167553
    logic [7:0] current_large_sum_ts1755425167553;
    always_comb begin
        current_large_sum_ts1755425167553 = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum_ts1755425167553 = current_large_sum_ts1755425167553 + inj_large_data_in_1755425167553_111[0];
            current_large_sum_ts1755425167553 = current_large_sum_ts1755425167553 + inj_large_data_in_1755425167553_111[1];
            current_large_sum_ts1755425167553 = current_large_sum_ts1755425167553 + 1;
        end
        inj_large_sum_out_1755425167553_885 = current_large_sum_ts1755425167553;
    end
    // END: loop_unroll_limit_test_ts1755425167553

    assign eq  = (in === tri_sig); 
    assign neq = (in !== tri_sig); 
endmodule


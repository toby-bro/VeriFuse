module loop_with_begin_end (
    input logic [2:0] count_limit,
    input logic [7:0] data_in,
    output logic [7:0] accumulated_xor
);
    logic [7:0] accum_xor_reg;
    always_comb begin
        accum_xor_reg = 8'hFF; 
        for (int iter = 0; iter < count_limit; iter = iter + 1) begin : loop_block
            accum_xor_reg = accum_xor_reg ^ data_in;
            accum_xor_reg = accum_xor_reg + 1;
        end
        accumulated_xor = accum_xor_reg;
    end
endmodule


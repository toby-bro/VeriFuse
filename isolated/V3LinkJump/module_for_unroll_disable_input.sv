module module_for_unroll_disable_input (
    input logic [3:0] in_limit,
    output logic [3:0] out_last_i
);
    always_comb begin: for_unroll_block
        out_last_i = 0;
        for (int i = 0; i < in_limit; i++) begin
            out_last_i = i;
        end
    end
endmodule


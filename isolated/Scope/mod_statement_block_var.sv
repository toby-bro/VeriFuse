module mod_statement_block_var (
    input logic in_c,
    output logic out_c
);
    always_comb begin : block_with_vars
        int   block_local_int;
        logic [7:0] block_local_logic;
        block_local_int   = in_c ? 10 : 20;
        block_local_logic = block_local_int;
        out_c             = block_local_logic[0];
    end
endmodule


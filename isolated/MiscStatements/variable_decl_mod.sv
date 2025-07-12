module variable_decl_mod (
    input logic data_in,
    output logic result_out
);
    static logic [7:0] module_static_var = 8'hAA;
    always_comb begin
        automatic logic proc_auto_var;
        static logic [7:0] block_var = 8'hBB;
        logic [7:0] another_block_var;
        proc_auto_var = data_in;
        another_block_var = {7'b0, data_in} + 1;
        result_out = block_var[0] ^ another_block_var[0] ^ module_static_var[7];
    end
endmodule


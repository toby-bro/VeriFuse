module ReplicationOps (
    input int count_in,
    input logic [7:0] vec_in,
    output logic [63:0] out_repl_const,
    output logic [63:0] out_repl_var
);
    assign out_repl_const = {8{vec_in}};
    always_comb begin
        integer idx;
        out_repl_var = '0;
        for (idx = 0; idx < (count_in > 8 ? 8 : count_in); idx = idx + 1) begin
            out_repl_var[idx*8 +: 8] = vec_in;
        end
    end
endmodule


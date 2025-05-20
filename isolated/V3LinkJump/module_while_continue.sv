module module_while_continue (
    input logic [3:0] in_skip,
    output logic [3:0] out_sum
);
    always_comb begin: while_cont_block
        logic [3:0] i;
        out_sum = 0;
        i = 0;
        while (i < 10) begin
            i = i + 1;
            if (i == in_skip) begin
                continue;
            end
            out_sum = out_sum + i;
        end
    end
endmodule


module module_while_break (
    input logic [3:0] in_limit,
    output logic [3:0] out_count
);
    always_comb begin: while_block
        logic [3:0] i;
        out_count = 0;
        i = 0;
        while (i < 10) begin
            if (i >= in_limit) begin
                break;
            end
            out_count = out_count + 1;
            i = i + 1;
        end
    end
endmodule


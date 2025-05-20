module module_nested_loops_break (
    input logic [1:0] in_outer_limit,
    input logic [1:0] in_inner_limit,
    output logic [3:0] out_value
);
    always_comb begin: nested_break_block
        logic [1:0] i, j;
        out_value = 0;
        i = 0;
        outer_loop: while (i < in_outer_limit) begin
            j = 0;
            inner_loop: while (j < in_inner_limit) begin
                if (i == 1 && j == 1) begin
                    break;
                end
                out_value = out_value + 1;
                j = j + 1;
            end
            i = i + 1;
        end
    end
endmodule


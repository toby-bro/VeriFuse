module mod_fork_join (
    input logic en,
    input int x,
    output int y1,
    output int y2
);
    always_comb begin
        y1 = 0;
        y2 = 0;
        if (en) begin
            fork : fork_block_name
                y1 = x;
                y2 = x + 1;
            join_none
        end
    end
endmodule


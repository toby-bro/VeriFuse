module module_nested_loop_jumps (
    input logic [3:0] inner_limit,
    input logic [3:0] outer_limit,
    output int out_count
);
    int count;
    always_comb begin
        count = 0;
        for (int i = 0; i < outer_limit; i++) begin
            for (int j = 0; j < inner_limit; j++) begin
                if (i == 1 && j == 1)
                    continue;
                if (i == 2 && j == 0)
                    break;
                if (i == 3 && j == 2)
                    break;
                count++;
            end
            if (i == 3)
                break;
        end
    end
    assign out_count = count;
endmodule


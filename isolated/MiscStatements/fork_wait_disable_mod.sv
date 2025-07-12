module fork_wait_disable_mod (
    input logic clk,
    input logic start_in,
    output logic done_out
);
    static logic task1_done = 0;
    static logic task2_done = 0;
    static logic inner_block_done = 0;
    task t1();
        @(posedge clk);
        task1_done = 1;
    endtask
    task t2();
        @(posedge clk);
        task2_done = 1;
    endtask
    always @(posedge clk) begin
        if (start_in) begin
            task1_done = 0;
            task2_done = 0;
            inner_block_done = 0;
            fork
                t1();
                t2();
                begin : inner_block
                    @(posedge clk);
                    inner_block_done = 1;
                end
            join_none
        end
    end
    always @(posedge clk) begin
        if (start_in) begin
            fork
                @(posedge clk);
                @(posedge clk);
                disable fork;
            join
            fork
                @(posedge clk);
                @(posedge clk);
                wait fork;
            join
            done_out = task1_done && task2_done && inner_block_done;
        end else begin
            done_out = 0;
        end
    end
endmodule


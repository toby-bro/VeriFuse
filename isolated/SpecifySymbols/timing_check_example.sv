module timing_check_example (
    input wire clk,
    input wire data,
    input wire en,
    input wire reset_n,
    output reg notifier
);
    always @(posedge clk) notifier <= 1'b0;
    specify
        $setup(posedge data, posedge clk, 10, notifier);
        $hold(negedge data, negedge clk, 5, notifier);
        $recovery(posedge reset_n, posedge clk, 8, notifier);
        $removal(negedge reset_n, negedge clk, 7, notifier);
        $skew(posedge data, posedge clk, 12, notifier);
        $setuphold(posedge data, posedge clk, 6, 8, notifier, en, reset_n, data, clk);
        $recrem(posedge data, posedge clk, 9, 11, notifier, en, reset_n, data, clk);
        $period(posedge clk, 20, notifier);
        $width(posedge data, 5, 6, notifier);
        $nochange(posedge clk, data, 10, 20, notifier);
    endspecify
endmodule


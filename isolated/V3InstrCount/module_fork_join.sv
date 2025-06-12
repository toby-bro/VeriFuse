module module_fork_join (
    output reg [7:0] out_fj_result,
    input wire in_fj_clk,
    input wire in_fj_start
);
    always_ff @(posedge in_fj_clk) begin
    if (in_fj_start) begin
        fork
            begin
                out_fj_result[3:0] <= 4'b1111;
            end
            begin
                out_fj_result[7:4] <= 4'b1010;
            end
        join
    end else begin
        out_fj_result <= 8'b0;
    end
    end
endmodule


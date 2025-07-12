module MiscExpressions_ClockingEventExpr (
    input logic clk,
    input int in_value,
    output int out_sampled_value
);
    clocking cb @(posedge clk); endclocking
    always_ff @(cb) begin
        out_sampled_value = $sampled(in_value); 
    end
endmodule


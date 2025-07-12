module timed_stmt_mod (
    input logic clk,
    input logic enable,
    output logic data_out
);
    static logic temp_data = 0;
    always @(posedge clk) begin
        if (enable) begin
            @(posedge clk) temp_data = ~temp_data;
        end
    end
    assign data_out = temp_data;
endmodule


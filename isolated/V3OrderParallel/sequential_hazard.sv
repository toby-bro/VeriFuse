module sequential_hazard (
    input wire clk,
    input wire enable_a,
    input wire enable_b,
    input wire [3:0] data_a,
    input wire [3:0] data_b,
    output wire [3:0] result_out
);
    reg [3:0] shared_reg;
    always @(posedge clk) begin
        if (enable_a) begin
            shared_reg <= data_a;
        end
    end
    always @(posedge clk) begin
        if (enable_b) begin
            shared_reg <= data_b;
        end
    end
    assign result_out = shared_reg;
endmodule


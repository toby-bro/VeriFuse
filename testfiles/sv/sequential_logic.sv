module sequential_logic (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       enable,
    input  logic [7:0] data,
    output logic [7:0] q
);
    // Simple sequential logic with flip-flop
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q <= 8'h00;
        end else if (enable) begin
            q <= data;
        end
    end
endmodule

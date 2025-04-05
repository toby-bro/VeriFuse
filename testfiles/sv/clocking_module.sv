module clocking_module (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    // Clocking block for synchronous sampling
    clocking cb @(posedge clk);
        input data_in;
        output data_out;
    endclocking
    
    // Always block using clock
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 8'h00;
        end else begin
            // Simple toggle operation
            data_out <= ~data_in;
        end
    end
endmodule

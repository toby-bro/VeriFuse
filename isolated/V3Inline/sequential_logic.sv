module sequential_logic (
    input logic clk,
    input logic [3:0] data_in,
    input logic rst_n,
    output logic [3:0] data_out
);
    /* verilator inline_module */;
    logic [3:0] internal_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= 4'h0;
        end else begin
            internal_reg <= data_in;
        end
    end
    assign data_out = internal_reg;
endmodule


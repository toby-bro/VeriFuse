module sequential_logic (
    input logic [3:0] data_in,
    output logic [3:0] data_out,
    input logic clk,
    input logic rst_n
);
    /* verilator no_inline_module */ ;
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


module sequential_register_en (
    input logic clk,
    input logic [7:0] data_in,
    input logic en,
    output logic [7:0] data_out
);
    always_ff @(posedge clk) begin
        if (en) begin
            data_out <= data_in;
        end
    end
endmodule


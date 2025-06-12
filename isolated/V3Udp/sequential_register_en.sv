module sequential_register_en (
    output logic [7:0] data_out,
    input logic clk,
    input logic en,
    input logic [7:0] data_in
);
    always_ff @(posedge clk) begin
        if (en) begin
            data_out <= data_in;
        end
    end
endmodule


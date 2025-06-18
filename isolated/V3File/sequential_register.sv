module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule


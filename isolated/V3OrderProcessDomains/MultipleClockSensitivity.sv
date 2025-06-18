module MultipleClockSensitivity (
    input logic clk_a,
    input logic clk_b,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic [7:0] data_combined
);
    logic [7:0] reg_a_q;
    logic [7:0] reg_b_q;
    always @(posedge clk_a or posedge clk_b) begin
        if (data_a > data_b) begin
            reg_a_q <= data_a;
            reg_b_q <= 8'h00;
        end else begin
            reg_a_q <= 8'h00;
            reg_b_q <= data_b;
        end
    end
    assign data_combined = reg_a_q | reg_b_q;
endmodule


module ModClockedConditional (
    input logic clk,
    input logic enable,
    input logic data_in,
    output logic data_out
);
    logic reg_data;
    always @(posedge clk) begin
    if (enable) begin
        reg_data <= data_in;
    end
    end
    assign data_out = reg_data;
endmodule


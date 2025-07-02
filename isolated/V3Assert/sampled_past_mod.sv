module sampled_past_mod (
    input logic clk,
    input logic [3:0] data_in,
    input logic reset,
    output logic [3:0] data_past_out,
    output logic [3:0] data_sampled_out
);
    logic [3:0] past_internal;
    always @(posedge clk) begin
        past_internal <= $past(data_in, 2);
    end
    assign data_past_out = past_internal;
    assign data_sampled_out = $sampled(data_in);
endmodule


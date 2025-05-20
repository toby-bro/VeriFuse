module split_independent_nb (
    input logic clk_f,
    input logic [7:0] in1_f,
    input logic [7:0] in2_f,
    input logic [7:0] in3_f,
    output logic [7:0] out1_f,
    output logic [7:0] out2_f,
    output logic [7:0] out3_f
);
    always @(posedge clk_f) begin
        out1_f <= in1_f;
        out2_f <= in2_f;
        out3_f <= in3_f;
    end
endmodule


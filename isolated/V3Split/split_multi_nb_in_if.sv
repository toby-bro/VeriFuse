module split_multi_nb_in_if (
    input logic [7:0] in4_dd,
    output logic [7:0] out1_dd,
    output logic [7:0] out2_dd,
    input logic clk_dd,
    input logic cond_dd,
    input logic [7:0] in1_dd,
    input logic [7:0] in2_dd,
    input logic [7:0] in3_dd
);
    always @(posedge clk_dd) begin
        if (cond_dd) begin
            out1_dd <= in1_dd + in2_dd;
            out2_dd <= in3_dd - in4_dd;
        end else begin
            out1_dd <= in1_dd * in2_dd;
            out2_dd <= in3_dd / (in4_dd + 1);
        end
    end
endmodule


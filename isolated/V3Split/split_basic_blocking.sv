module split_basic_blocking (
    output logic [7:0] out1_a,
    input logic [7:0] in1_a
);
    always @(*) begin
        out1_a = in1_a;
    end
endmodule


module split_basic_blocking (
    input logic [7:0] in1_a,
    output logic [7:0] out1_a
);
    always @(*) begin
        out1_a = in1_a;
    end
endmodule


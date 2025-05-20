module comb_simple (
    input bit [7:0] in1,
    input bit [7:0] in2,
    output bit [7:0] out1,
    output bit [7:0] out2
);
    always @* begin
    out1 = in1 & in2;
    out2 = in1 | in2;
      end
endmodule


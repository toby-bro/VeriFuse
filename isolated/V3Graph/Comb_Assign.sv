module Comb_Assign (
    output wire out,
    input wire in1,
    input wire in2
);
    assign out = in1 & in2;
endmodule


module remaining_reduction_ops (
    output logic nand_out,
    output logic nor_out,
    output logic xnor_out,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3
);
    assign nand_out = ~&in1;
    assign nor_out = ~|in2;
    assign xnor_out = ^~in3;
endmodule


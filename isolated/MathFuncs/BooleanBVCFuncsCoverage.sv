module BooleanBVCFuncsCoverage (
    input logic [3:0] vector_in,
    output bit isunknown_out,
    output bit onehot0_out,
    output bit onehot_out
);
always @(*) begin
    onehot_out = $onehot(vector_in);
    onehot0_out = $onehot0(vector_in);
    isunknown_out = $isunknown(vector_in);
end
endmodule


module CountOnesCoverage (
    input logic [15:0] vector_in,
    output int countones_out
);
always @(*) begin
    countones_out = $countones(vector_in);
end
endmodule


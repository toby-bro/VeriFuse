module split_single_stmt (
    input logic [7:0] in_q,
    output logic [7:0] out_q
);
    always @(*) begin
        out_q = in_q + 1;
    end
endmodule


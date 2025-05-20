module combinatorial_logic (
    input logic [3:0] in_vector,
    output logic out_single
);
    always_comb begin
        if (in_vector > 4'd5) begin
            out_single = 1'b1;
        end else begin
            out_single = 1'b0;
        end
    end
endmodule


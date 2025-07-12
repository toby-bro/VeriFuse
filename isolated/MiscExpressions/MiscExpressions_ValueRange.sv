module MiscExpressions_ValueRange (
    input logic [15:0] in_vector,
    output logic [7:0] out_slice
);
    always_comb begin
        out_slice = in_vector[7:0];
    end
endmodule


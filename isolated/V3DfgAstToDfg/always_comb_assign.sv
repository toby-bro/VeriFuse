module always_comb_assign (
    input logic [15:0] in,
    output logic [15:0] out
);
    always_comb begin
        out = in;
    end
endmodule


module always_comb_assign (
    output logic [15:0] out,
    input logic [15:0] in
);
    always_comb begin
        out = in;
    end
endmodule


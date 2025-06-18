module mod_comb_logic (
    input logic a,
    input logic b,
    output logic y
);
    always_comb begin
        y = a & b;
    end
endmodule


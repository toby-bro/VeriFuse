module mod_comb_logic (
    output logic y,
    input logic a,
    input logic b
);
    always_comb begin
        y = a & b;
    end
endmodule


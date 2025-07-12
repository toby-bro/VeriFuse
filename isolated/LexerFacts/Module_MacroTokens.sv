module Module_MacroTokens (
    input logic tok_in,
    output logic tok_out
);
    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = tok_in;
        tok_out         = `PASTE(my,_var);
    end
endmodule


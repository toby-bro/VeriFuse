module StringAtoRealMod (
    input string s_in_real,
    output real out_real
);
    always @(*) begin
        out_real = s_in_real.atoreal();
    end
endmodule


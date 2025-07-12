module StringAtoIMod (
    input string s_in_bin,
    input string s_in_hex,
    input string s_in_int,
    input string s_in_oct,
    output int out_bin,
    output int out_hex,
    output int out_int,
    output int out_oct
);
    always @(*) begin
        out_int = s_in_int.atoi();
        out_hex = s_in_hex.atohex();
        out_oct = s_in_oct.atooct();
        out_bin = s_in_bin.atobin();
    end
endmodule


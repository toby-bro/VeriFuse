module StringItoAMod (
    input logic [31:0] val_bin,
    input logic [31:0] val_hex,
    input int val_int,
    input logic [31:0] val_oct,
    output string s_out_bin,
    output string s_out_hex,
    output string s_out_int,
    output string s_out_oct
);
    var string temp_string = ""; 
    always @(*) begin
        temp_string.itoa(val_int);
        s_out_int = temp_string;
        temp_string.hextoa(val_hex);
        s_out_hex = temp_string;
        temp_string.octtoa(val_oct);
        s_out_oct = temp_string;
        temp_string.bintoa(val_bin);
        s_out_bin = temp_string;
    end
endmodule


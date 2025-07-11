module StringLenMod (
    input string input_string,
    output int   string_length
);
    always @(*) begin
        string_length = input_string.len();
    end
endmodule
module StringPutcGetcMod (
    input string input_string,
    input int    put_index,
    input byte   char_to_put,
    input int    get_index,
    output string modified_string,
    output byte   char_gotten
);
    var string temp_string;
    always @(*) begin
        temp_string = input_string;
        if (put_index >= 0 && put_index < temp_string.len()) begin
            temp_string.putc(put_index, char_to_put);
        end
        modified_string = temp_string;
        if (get_index >= 0 && get_index < temp_string.len()) begin
            char_gotten = temp_string.getc(get_index);
        end else begin
            char_gotten = 8'h00; 
        end
    end
endmodule
module StringCaseMod (
    input string input_string,
    output string upper_string,
    output string lower_string
);
    always @(*) begin
        upper_string = input_string.toupper();
        lower_string = input_string.tolower();
    end
endmodule
module StringCompareMod (
    input string s1,
    input string s2,
    output int   compare_result,
    output int   icompare_result
);
    always @(*) begin
        compare_result = s1.compare(s2);
        icompare_result = s1.icompare(s2);
    end
endmodule
module StringSubstrMod (
    input string input_string,
    input int    left_index,
    input int    right_index,
    output string substring_result
);
    always @(*) begin
        substring_result = input_string.substr(left_index, right_index);
    end
endmodule
module StringAtoIMod (
    input string s_in_int,
    input string s_in_hex,
    input string s_in_oct,
    input string s_in_bin,
    output int   out_int,
    output int   out_hex,
    output int   out_oct,
    output int   out_bin
);
    always @(*) begin
        out_int = s_in_int.atoi();
        out_hex = s_in_hex.atohex();
        out_oct = s_in_oct.atooct();
        out_bin = s_in_bin.atobin();
    end
endmodule
module StringAtoRealMod (
    input string s_in_real,
    output real  out_real
);
    always @(*) begin
        out_real = s_in_real.atoreal();
    end
endmodule
module StringItoAMod (
    input int           val_int,
    input logic [31:0]  val_hex,
    input logic [31:0]  val_oct,
    input logic [31:0]  val_bin,
    output string       s_out_int,
    output string       s_out_hex,
    output string       s_out_oct,
    output string       s_out_bin
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
module StringRealtoAMod (
    input real   val_real,
    output string s_out_real
);
    var string temp_string = ""; 
    always @(*) begin
        temp_string.realtoa(val_real);
        s_out_real = temp_string;
    end
endmodule

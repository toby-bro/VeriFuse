module builtin_string_method (
    input string in_string,
    input int index_in_getc,
    input int index_in_substr_end,
    input int index_in_substr_start,
    output byte out_char,
    output int out_len,
    output string out_substr_val,
    output string out_upper_val
);
    always_comb begin
        out_len = in_string.len(); 
        if (index_in_getc >= 0 && index_in_getc < in_string.len()) begin
            out_char = in_string.getc(index_in_getc);
        end else begin
            out_char = 0;
        end
        if (index_in_substr_start >= 0 && index_in_substr_end >= 0 &&
            index_in_substr_start < in_string.len() && index_in_substr_end < in_string.len() &&
            index_in_substr_start <= index_in_substr_end) begin
                out_substr_val = in_string.substr(index_in_substr_start, index_in_substr_end);
        end else begin
            out_substr_val = "";
        end
        out_upper_val = in_string.toupper();
    end
endmodule


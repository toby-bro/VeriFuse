module StringPutcGetcMod (
    input byte char_to_put,
    input int get_index,
    input string input_string,
    input int put_index,
    output byte char_gotten,
    output string modified_string
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


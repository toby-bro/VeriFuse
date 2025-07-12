module StringCaseMod (
    input string input_string,
    output string lower_string,
    output string upper_string
);
    always @(*) begin
        upper_string = input_string.toupper();
        lower_string = input_string.tolower();
    end
endmodule


module StringLenMod (
    input string input_string,
    output int string_length
);
    always @(*) begin
        string_length = input_string.len();
    end
endmodule


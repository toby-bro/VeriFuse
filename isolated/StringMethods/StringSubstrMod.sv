module StringSubstrMod (
    input string input_string,
    input int left_index,
    input int right_index,
    output string substring_result
);
    always @(*) begin
        substring_result = input_string.substr(left_index, right_index);
    end
endmodule


module element_select_string (
    input string in_string,
    input int index_in,
    output byte out_byte
);
    always_comb begin
        if (index_in >= 0 && index_in < in_string.len())
            out_byte = in_string[index_in];
        else
            out_byte = 0; 
    end
endmodule


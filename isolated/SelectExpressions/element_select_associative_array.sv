module element_select_associative_array (
    input string in_key,
    input int in_val,
    input string lookup_key,
    output int out_val
);
    int aa_var[string]; 
    always_comb begin
        aa_var[in_key] = in_val;
        out_val = aa_var[lookup_key]; 
    end
endmodule


module element_select_dynamic_array (
    input int in_size,
    input int in_val,
    input int index_in,
    output int da_size,
    output int out_val
);
    int da_var[]; 
    always_comb begin
        if (in_size > 0) da_var = new[in_size];
        else da_var = new[0];
        if (index_in >= 0 && index_in < da_var.size()) da_var[index_in] = in_val;
        da_size = da_var.size(); 
        if (index_in >= 0 && index_in < da_size)
            out_val = da_var[index_in];
        else
            out_val = 0; 
    end
endmodule


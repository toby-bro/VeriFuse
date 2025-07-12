module builtin_array_method (
    input int lookup_val,
    output bit out_found,
    output int out_index,
    output int out_min,
    output int out_size,
    output int out_sum
);
    int da_var[]; 
    always_comb begin
        static int min_val;
        int idx_arr[];
        da_var = new[5]; 
        foreach(da_var[i]) da_var[i] = i * 10; 
        out_size = da_var.size(); 
        min_val = da_var[0];
        foreach(da_var[i]) if (da_var[i] < min_val) min_val = da_var[i];
        out_min = min_val;
        out_sum = da_var.sum(); 
        out_found = (da_var.find() with (item == lookup_val)).size() > 0; 
        idx_arr = da_var.find_index() with (item == lookup_val); 
        if (idx_arr.size() > 0) out_index = idx_arr[0];
        else out_index = -1;
    end
endmodule


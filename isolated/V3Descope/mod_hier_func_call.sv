module mod_hier_func_call (
    input logic i_value,
    output logic o_processed_value
);
    
    function automatic logic process_it (input logic val_in);
        return ~val_in;
    endfunction : process_it
    
    always_comb begin
        o_processed_value = process_it(i_value);
    end
    
endmodule


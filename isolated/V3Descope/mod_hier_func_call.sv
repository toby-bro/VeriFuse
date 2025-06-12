module mod_hier_func_call (
    output logic o_processed_value,
    input logic i_value
);
    my_func_scope: begin
        function automatic logic process_it (input logic val_in);
            return ~val_in;
        endfunction : process_it
    end : my_func_scope
    always_comb begin
        o_processed_value = my_func_scope.process_it(i_value);
    end
endmodule


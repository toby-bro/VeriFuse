module ModuleWithAttributes (
    (* my_port_attr *) input bit attr_in,
    output bit attr_out
);
    (* my_param_attr *) parameter int P_ATTR = 5;
    (* my_var_attr = 123 *) logic var_attr;
    (* my_func_attr *) function bit process_attr (bit i);
        return i;
    endfunction
    assign var_attr  = attr_in;
    assign attr_out  = process_attr(var_attr);
endmodule


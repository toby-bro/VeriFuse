module Module_Hierarchical (
    input bit h_in,
    output bit h_out
);
    int cu_var_read;
    assign h_out = h_in;
    always_comb begin
        cu_var_read = $unit::compilation_unit_var;
    end
endmodule


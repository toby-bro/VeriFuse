module mod_constraint_block (
    input int input_data,
    output bit constraint_ok
);
    always_comb begin
        if (input_data >= 0 && input_data <= 10)
            constraint_ok = 1;
        else
            constraint_ok = 0;
    end
    assert (input_data != 42);
endmodule


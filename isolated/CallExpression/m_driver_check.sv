module m_driver_check (
    input bit clk,
    input int val_in,
    output int driven_var
);
    int my_driven_var;
    function automatic void write_to_var(input int val);
        my_driven_var = val;
    endfunction
    always @(posedge clk) begin
        write_to_var(val_in);
    end
    assign driven_var = my_driven_var;
endmodule


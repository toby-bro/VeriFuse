module mod_named_begin (
    output int data_out,
    input int data_in
);
    always_comb begin : my_named_block
        data_out = data_in;
    end
endmodule


module mod_specify (
    input wire i_in_bit,
    input wire j_in_bit,
    output wire o_out_bit
);
    specparam sp_delay = 10;
    specify
        (i_in_bit => o_out_bit) = sp_delay;
        $setup(i_in_bit, j_in_bit, 5);
    endspecify
    assign o_out_bit = i_in_bit ^ j_in_bit;
endmodule


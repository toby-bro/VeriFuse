module attributes_test (
    input logic i_attr_in,
    output logic o_attr_out
);
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = i_attr_in ? 1'b1 : 1'b0;
        o_attr_out      = internal_signal;
    end
endmodule


module named_block_logic (
    output logic o_out,
    input logic i_in,
    input logic i_gate
);
    logic r_internal;
    logic r_temp;
    always_comb begin : my_combinational_block
        r_temp = i_in & i_gate;
        r_internal = r_temp;
        o_out = r_internal;
    end
endmodule


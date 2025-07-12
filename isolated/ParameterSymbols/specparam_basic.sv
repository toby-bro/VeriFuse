module specparam_basic (
    input wire i_data_in,
    output logic o_data_out
);
    specify
        specparam basic_delay = 5;
        (i_data_in => o_data_out) = basic_delay;
    endspecify
    always_comb begin
        o_data_out = i_data_in;
    end
endmodule


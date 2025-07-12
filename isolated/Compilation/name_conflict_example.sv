module name_conflict_example (
    input logic i_in,
    output logic o_out
);
    parameter int my_param = 5;
    logic my_var;
    always_comb my_var = i_in;
    assign o_out = i_in && (my_param == 5) && my_var;
endmodule


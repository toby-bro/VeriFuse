module HandleConstantsAndEquality (
    output logic o_neq_q,
    output logic o_eqwild_q,
    output logic o_neqwild_q,
    input logic [7:0] i_data,
    output logic o_eq_q
);
    parameter P_X_CONST = 8'hXX;
    parameter P_Z_CONST = 8'hZZ;
    parameter P_0_X_CONST = 8'b0101_X10X;
    assign o_eq_q = (i_data ==? P_0_X_CONST);
    assign o_neq_q = (i_data !=? P_0_X_CONST);
    assign o_eqwild_q = (i_data ==? P_X_CONST);
    assign o_neqwild_q = (i_data !=? P_Z_CONST);
endmodule


module equality_ops (
    output logic neq,
    output logic case_eq,
    output logic case_neq,
    input logic [7:0] a,
    input logic [7:0] b,
    output logic eq
);
    localparam logic [7:0] Z_VAL = 'z;
    localparam logic [7:0] X_VAL = 'x;
    assign eq = a == b;
    assign neq = a != b;
    assign case_eq = (a ==? Z_VAL);
    assign case_neq = (b !=? X_VAL);
endmodule


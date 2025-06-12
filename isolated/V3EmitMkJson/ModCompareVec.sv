module ModCompareVec (
    input logic [3:0] v1,
    input logic [3:0] v2,
    output logic eq
);
    assign eq = (v1 == v2);
endmodule


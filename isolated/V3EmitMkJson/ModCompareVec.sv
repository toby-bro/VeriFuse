module ModCompareVec (
    input logic [3:0] v2,
    output logic eq,
    input logic [3:0] v1
);
    assign eq = (v1 == v2);
endmodule


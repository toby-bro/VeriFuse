module ModSimpleLogic (
    input logic b,
    output logic y,
    input logic a
);
    assign y = a ^ b;
endmodule


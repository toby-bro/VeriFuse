module ValidTimeScaleModuleDecl (
    input logic in_vts,
    output logic out_vts
);
    timeunit      1ns;
    timeprecision 1ps;
    assign out_vts = in_vts;
endmodule


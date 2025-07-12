module ModuleImplicitPort (
    input logic signed [7:0] data,
    output logic out_valid
);
    logic valid;
    assign valid = |data;
    assign out_valid = valid;
endmodule


module always_multi_stmt_unhandled (
    output logic [7:0] out2,
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1
);
    always_comb begin
        out1 = in1;
        out2 = in2;
    end
endmodule


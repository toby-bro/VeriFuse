module child_simple (
    input logic in1,
    output logic out1,
    inout wire io1
);
    assign io1 = in1 & out1;
    always_comb begin
        out1 = in1 ^ io1;
    end
endmodule


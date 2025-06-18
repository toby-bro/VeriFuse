module basic_comb (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1
);
    ;
    logic [7:0] temp_wire;
    assign temp_wire = in1 + in2;
    always_comb begin
        out1 = temp_wire;
    end
endmodule


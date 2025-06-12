module ModuleComb (
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2,
    input logic [7:0] in1
);
    logic [7:0] internal_wire;
    assign internal_wire = in1 + in2;
    always_comb begin
        if (internal_wire > 8'd128) begin
            out1 = internal_wire - 1;
        end else begin
            out1 = internal_wire + 1;
        end
        out2 = internal_wire / 2;
    end
endmodule


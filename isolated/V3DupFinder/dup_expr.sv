module dup_expr (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    logic [7:0] temp_add;
    logic [7:0] temp_mult;
    logic [7:0] inter1;
    logic [7:0] inter2;
    logic [7:0] complex_expr;
    always_comb begin
        temp_add = in1 + in2;
        out1 = temp_add;
        out2 = in1 + in2;
        inter1 = in1 * 2;
        inter2 = in2 * 2;
        temp_mult = inter1 + inter2;
        complex_expr = (in1 + in2) * (in1 - in2) + (in1 + in2);
        if (in1 > in2) begin
            out1 = temp_mult;
        end else begin
            out1 = temp_add;
        end
        if (in2 >= in1) begin
            out2 = temp_add;
        end else begin
            out2 = temp_mult;
        end
        out1 = out1 + complex_expr;
    end
endmodule


module ModSimpleLogic(
    input logic a,
    input logic b,
    output logic y
);
    assign y = a ^ b;
endmodule
module ModVectorAdd(
    input logic [7:0] in_v,
    output logic [7:0] out_v
);
    assign out_v = in_v + 8'h01;
endmodule
module ModCompareVec(
    input logic [3:0] v1,
    input logic [3:0] v2,
    output logic eq
);
    assign eq = (v1 == v2);
endmodule
module ModRegister(
    input logic din,
    output logic dout
);
    always @* begin
        dout = din;
    end
endmodule
module ModWideBus(
    input logic [31:0] data_in_w,
    output logic [31:0] data_out_w
);
    assign data_out_w = ~data_in_w;
endmodule

module ModuleBasicVar (
    input logic [7:0] in1,
    input int in2,
    output logic [7:0] out1,
    output int out2,
    output real out3,
    output int out5
);
    logic [7:0] var1 = in1 + 1;
    int var2;
    real var3 = 3.14;
    logic [3:0][15:0] var4 = '0;
    int var5 = '1;
    assign var2 = in2 * 2;
    assign out1 = var1;
    assign out2 = var2;
    assign out3 = var3;
    assign out4 = var4;
    assign out5 = var5;
endmodule


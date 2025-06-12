interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
module ModuleWithInterface (
    input logic clk_in,
    output logic valid_out
);
    MyInterface my_if (clk_in);
    assign my_if.req = 1'b1;
    assign valid_out = my_if.valid;
endmodule


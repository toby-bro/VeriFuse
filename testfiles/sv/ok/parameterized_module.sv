module parameterized_module #(
    parameter WIDTH = 8,
    parameter INIT_VALUE = 0
) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    // Module with parameters
    assign out = (in == 0) ? INIT_VALUE : in;
endmodule

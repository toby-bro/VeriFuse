module module_with_params #(
    parameter integer DATA_WIDTH = 8
) (
    output wire [7:0] param_out,
    input wire [7:0] param_in
);
    assign param_out = param_in;
endmodule


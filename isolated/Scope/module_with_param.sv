module module_with_param (
    input logic in,
    output logic named_out
);
    parameter int DELAY = 10;
    logic bind_dummy_in;
    logic bind_dummy_out;
    assign named_out = in;
endmodule


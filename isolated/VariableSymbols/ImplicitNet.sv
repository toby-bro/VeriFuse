module ImplicitNet (
    input logic in_val,
    output wire out_val
);
    assign implicit_wire = in_val;
    assign out_val = implicit_wire;
endmodule


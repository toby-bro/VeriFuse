module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module DummyBindTarget (
    input bit d_in,
    output bit d_out
);
    assign d_out = d_in;
    BindSimpleModule u_bind (.in(d_in), .out());
endmodule


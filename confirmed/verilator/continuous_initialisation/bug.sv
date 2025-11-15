module bug(
    input bit in,
    input bit in2,
    output bit out
);
    bit internal = in;
    assign out = internal | in2;
endmodule

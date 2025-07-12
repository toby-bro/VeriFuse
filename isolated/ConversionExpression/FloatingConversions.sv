module FloatingConversions (
    input int in_int,
    input real in_real,
    output shortreal out_float_from_int,
    output longint out_int_from_real
);
    always_comb begin
        out_int_from_real  = longint'(in_real);
        out_float_from_int = shortreal'(in_int);
    end
endmodule


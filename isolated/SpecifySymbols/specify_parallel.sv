module specify_parallel (
    input wire [3:0] vec_in,
    output wire [3:0] vec_out
);
    assign vec_out = vec_in;
    specparam full_delay = 4;
    specify
        (vec_in *> vec_out) = full_delay;
    endspecify
endmodule


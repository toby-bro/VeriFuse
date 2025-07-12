module child_defaults (
    input logic dummy_in,
    output bit flag_out
);
    always_comb begin
        flag_out = (val_in > 5) ^ dummy_in;
    end
endmodule


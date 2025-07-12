module ShortRealBitsConversion (
    input int in_iub,
    input shortreal in_sr,
    output shortreal out_bisr,
    output int out_srib
);
    always_comb begin
        out_srib = $shortrealtobits(in_sr);
        out_bisr = $bitstoshortreal(in_iub);
    end
endmodule


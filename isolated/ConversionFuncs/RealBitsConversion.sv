module RealBitsConversion (
    input longint in_lib,
    input real in_r,
    output real out_bir,
    output longint out_rib
);
    always_comb begin
        out_rib = $realtobits(in_r);
        out_bir = $bitstoreal(in_lib);
    end
endmodule


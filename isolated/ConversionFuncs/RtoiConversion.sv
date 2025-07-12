module RtoiConversion (
    input real in_r,
    output integer out_i
);
    always_comb begin
        out_i = $rtoi(in_r);
    end
endmodule


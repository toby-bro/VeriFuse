module ItorConversion (
    input integer in_i,
    input logic [63:0] in_l64,
    input logic signed [19:0] in_s20,
    output real out_r_from_i,
    output real out_r_from_l64,
    output real out_r_from_s20
);
    always_comb begin
        out_r_from_i = $itor(in_i);
        out_r_from_l64 = $itor(in_l64);
        out_r_from_s20 = $itor(in_s20);
    end
endmodule

